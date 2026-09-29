-- Prove2me | solution 1 for ModularCurve.DRResolvedModelPackage.DRResolvedModelCharts.exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/654f0615-80c3-5620-9951-d0e246def42c

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_ModularCurve_DRResolvedModelCharts
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_and_pullback_iso_of_isIso_app
import Theorems.Thm_AlgebraicGeometry_Scheme_bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_specialFibrePackage_of_chartTable
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ev_app_tensorUnit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_foldr_twist_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isOpenImmersion
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

universe u v

p2m_open "CategoryTheory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso IsLocallyNoetherian IsOpenImmersion.lift Scheme.IdealSheafData.coe_support_ofIdealTop Scheme.IdealSheafData.support_comap isIso_iff_isOpenImmersion_and_surjective IsProper morphismRestrict_ι Scheme.IdealSheafData.comap_comp Scheme.Modules.pullback Scheme.Opens.range_ι Scheme.Hom Scheme.Pullback.range_map Scheme.IdealSheafData.top_mul morphismRestrictRestrict Scheme.homOfLE_apply' Scheme.Hom.image_preimage_eq_opensRange_inf Scheme.Hom.support_ker IsZariskiLocalAtTarget LocallyOfFiniteType Spec IsIntegral Spec.map Scheme IsOpenImmersion Scheme.Hom.comp_base Flat Scheme.zeroLocus_span isIntegral_of_isOpenImmersion IsClosedImmersion IsSeparated Scheme.mem_zeroLocus_iff Scheme.Hom.opensRange_of_isIso morphismRestrict_base Scheme.Modules.pullbackCongr IsOpenImmersion.isoOfRangeEq IsZariskiLocalAtTarget.of_iSup_eq_top Scheme.IdealSheafData.support_eq_bot_iff Scheme.Modules FormallyUnramified Scheme.Opens Scheme.homOfLE_ι Scheme.Hom.id_base Flat.generalizingMap morphismRestrictEq Scheme.Hom.comp_preimage Scheme.IdealSheafData.ofIdealTop IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Opens.opensRange_ι Scheme.Hom.comp_apply basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.Modules.pullbackComp IsOpenImmersion.isoOfRangeEq_hom_fac Scheme.ΓSpecIso Scheme.Hom.coe_opensRange Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule Scheme.Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app Scheme.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk Scheme.Hom.isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map Scheme.Modules.IsInvertible.isIso_ev_app_tensorUnit Scheme.Modules.nonempty_pullback_foldr_twist_iso Scheme.IdealSheafData.IsInvertible.comap_of_isOpenImmersion Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.ker_comp_of_isIso IdealSheafData.coe_support_ofIdealTop IdealSheafData.support_comap ringCatSheaf IdealSheafData.comap_comp Modules.pullback Opens.range_ι Hom mk Γ empty Pullback.range_map IdealSheafData.top_mul homOfLE_apply' Hom.image_preimage_eq_opensRange_inf Hom.support_ker Hom.comp_base zeroLocus_span mem_zeroLocus_iff Hom.opensRange_of_isIso basicOpen Modules.pullbackCongr mk.injEq IdealSheafData.support_eq_bot_iff Modules IdealSheafData.comap Opens homOfLE_ι Hom.id_base Hom.comp_preimage le_iff_specializes IdealSheafData.ofIdealTop Opens.opensRange_ι restrict Hom.comp_apply IdealSheafData Modules.pullbackComp ΓSpecIso Hom.coe_opensRange Modules.IsInvertible Modules.pullbackUnitIso IdealSheafData.IsInvertible IdealSheafData.module IdealSheafData.invModule Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk Hom.isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map Modules.IsInvertible.isIso_ev_app_tensorUnit Modules.nonempty_pullback_foldr_twist_iso IdealSheafData.IsInvertible.comap_of_isOpenImmersion Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback presheaf Hom pullbackCongr restrict pullbackComp IsInvertible pullbackUnitIso IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app IsInvertible.isIso_ev_app_tensorUnit nonempty_pullback_foldr_twist_iso" namespace IsInvertible p2m_export "AlgebraicGeometry.Scheme.Modules.IsInvertible" "pullback mk exists_isInvertible_and_pullback_iso_of_isIso_app isIso_ev_app_tensorUnit" end AlgebraicGeometry.Scheme.Modules.IsInvertible
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.IsInvertible" in

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_forall_exists_trivial_nhd
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIntegral Y] [IsLocallyNoetherian X]
    (U : X.Opens) (hU : IsIso (f ∣_ U))
    {N : Type v} (x : N → X) (hcover : ∀ y : X, y ∉ U → ∃ n, y = x n)
    (W : N → X.Opens) (hxW : ∀ n, x n ∈ W n) (hWx : ∀ n m, m ≠ n → x m ∉ W n)
    (hnorm : ∀ n (y : X), y ∈ W n → IsDomain (X.presheaf.stalk y) ∧ IsIntegrallyClosed (X.presheaf.stalk y))
    (hdim : ∀ n, ¬ ringKrullDim (X.presheaf.stalk (x n)) ≤ 1)
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hloc : ∀ n, ∃ V : X.Opens, x n ∈ V ∧ V ≤ W n ∧
      Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj L ≅ SheafOfModules.unit (f ⁻¹ᵁ V).toScheme.ringCatSheaf)) :
    ∃ M : X.Modules, Scheme.Modules.IsInvertible M ∧ Nonempty ((Scheme.Modules.pullback f).obj M ≅ L) := by
  choose V hxV hVW hτ using hloc

  have hH : ∀ n (y : X), y ∈ V n → ringKrullDim (X.presheaf.stalk y) ≤ 1 → y ∈ U := by
    intro n y hy hd
    by_contra hyU
    obtain ⟨m, rfl⟩ := hcover y hyU
    by_cases hmn : m = n
    · subst hmn; exact hdim m hd
    · exact hWx n m hmn (hVW n hy)
  have hO : ∀ n (V' : X.Opens), V' ≤ V n → IsIso (f.app V') := fun n V' hV' =>
    Scheme.Hom.isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map f U hU V'
      (Scheme.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk V' U
        (fun y hy => hnorm n y (hVW n (hV' hy))) (fun y hy hd => hH n y (hV' hy) hd))
  have hcov : U ⊔ ⨆ n, V n = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    rw [Opens.mem_sup, Opens.mem_iSup]
    by_cases hy : y ∈ U
    · exact Or.inl hy
    · obtain ⟨n, rfl⟩ := hcover y hy
      exact Or.inr ⟨n, hxV n⟩
  exact Scheme.Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app f U hU V hcov hO L hL hτ

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso IsLocallyNoetherian IsOpenImmersion.lift Scheme.IdealSheafData.coe_support_ofIdealTop Scheme.IdealSheafData.support_comap isIso_iff_isOpenImmersion_and_surjective IsProper morphismRestrict_ι Scheme.IdealSheafData.comap_comp Scheme.Modules.pullback Scheme.Opens.range_ι Scheme.Hom Scheme.Pullback.range_map Scheme.IdealSheafData.top_mul morphismRestrictRestrict Scheme.homOfLE_apply' Scheme.Hom.image_preimage_eq_opensRange_inf Scheme.Hom.support_ker IsZariskiLocalAtTarget LocallyOfFiniteType Spec IsIntegral Spec.map Scheme IsOpenImmersion Scheme.Hom.comp_base Flat Scheme.zeroLocus_span isIntegral_of_isOpenImmersion IsClosedImmersion IsSeparated Scheme.mem_zeroLocus_iff Scheme.Hom.opensRange_of_isIso morphismRestrict_base Scheme.Modules.pullbackCongr IsOpenImmersion.isoOfRangeEq IsZariskiLocalAtTarget.of_iSup_eq_top Scheme.IdealSheafData.support_eq_bot_iff Scheme.Modules FormallyUnramified Scheme.Opens Scheme.homOfLE_ι Scheme.Hom.id_base Flat.generalizingMap morphismRestrictEq Scheme.Hom.comp_preimage Scheme.IdealSheafData.ofIdealTop IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Opens.opensRange_ι Scheme.Hom.comp_apply basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.Modules.pullbackComp IsOpenImmersion.isoOfRangeEq_hom_fac Scheme.ΓSpecIso Scheme.Hom.coe_opensRange Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule Scheme.Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app Scheme.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk Scheme.Hom.isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map Scheme.Modules.IsInvertible.isIso_ev_app_tensorUnit Scheme.Modules.nonempty_pullback_foldr_twist_iso Scheme.IdealSheafData.IsInvertible.comap_of_isOpenImmersion Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens" end AlgebraicGeometry
p2m_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.isIso_morphismRestrict_sup {X Y : Scheme.{u}} (f : Y ⟶ X) (A B : X.Opens)
    (hA : IsIso (f ∣_ A)) (hB : IsIso (f ∣_ B)) : IsIso (f ∣_ (A ⊔ B)) := by
  let W : X.Opens := A ⊔ B
  let V : Bool → W.toScheme.Opens := fun b => cond b (W.ι ⁻¹ᵁ A) (W.ι ⁻¹ᵁ B)
  have hcov : iSup V = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    rw [Opens.mem_iSup]
    rcases Opens.mem_sup.mp hy with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  have himg : ∀ b, W.ι ''ᵁ V b = cond b A B := by
    intro b
    cases b <;>
    · simp only [V, cond]
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right]
      first | exact le_sup_left | exact le_sup_right
  have key : ∀ b, (MorphismProperty.isomorphisms Scheme) ((f ∣_ W) ∣_ V b) := by
    intro b
    refine ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict f W (V b) ≪≫ morphismRestrictEq f (himg b))).mpr ?_
    cases b
    · exact hB
    · exact hA
  exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) V hcov key

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRResolvedModelPackage.chainPos DRModel.baseChangeMap DRResolvedModelPackage DRModel DRModel.toBase DRModelPackage X0MqComponents x0MqAdj x0MqAdj_symm x0MqResolvedTable DRResolvedModelPackage.DRResolvedModelCharts"
p2m_open "ModularCurve"

variable {p : ℕ} [Fact p.Prime]

namespace DRModelPackage p2m_export "ModularCurve.DRModelPackage" "smoothLocus isProper normal flat compZero isIntegral compInf mk.injEq mk w" end DRModelPackage
p2m_open_scoped "ModularCurve.DRModelPackage" in

abbrev DRModelPackage.XO (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] : Scheme.{0} :=
  pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))

namespace DRModelPackage
p2m_open_scoped "ModularCurve.DRModelPackage" in

private def _root_.ModularCurve.DRModelPackage.isoLocus (𝔛 : DRModelPackage p) (O : Type) [CommRing O] : (DRModelPackage.XO p O).Opens :=
  (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) ⁻¹ᵁ 𝔛.smoothLocus) ⊔
    (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))

end DRModelPackage
p2m_export "ModularCurve" "DRModelPackage.isoLocus"
namespace DRResolvedModelPackage
p2m_export "ModularCurve.DRResolvedModelPackage" "chainPos toBase toDR_iso_smoothLocus node toDR_over isIntegral node_fintype comp_isInvertible width mk.injEq mk Y nodeEquiv toDR_iso_generic regular node_deq edgePt smoothOffEdges exc_image flat isProper one_le_width edgePt_over comp toDR crossingPt DRResolvedModelCharts"
p2m_open "ModularCurve.DRResolvedModelPackage"

p2m_open "MvPolynomial P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.MvPolynomial MvPolynomial.CrossingQuotient P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.MvPolynomial.CrossingQuotient CategoryTheory.MonoidalCategory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory.MonoidalCategory"

variable {𝔛 : DRModelPackage p} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
  (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ)

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem isIso_toDR_restrict_isoLocus : IsIso (𝔛reg.toDR ∣_ 𝔛.isoLocus O) :=
  AlgebraicGeometry.isIso_morphismRestrict_sup _ _ _ 𝔛reg.toDR_iso_smoothLocus 𝔛reg.toDR_iso_generic

private abbrev _root_.ModularCurve.DRResolvedModelPackage.ChartWitness (ϖ : O) (Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ϖ e).IdealSheafData) :=
  𝔛reg.DRResolvedModelCharts ϖ Fc

p2m_export "ModularCurve.DRResolvedModelPackage" "ChartWitness"

private noncomputable def _root_.ModularCurve.DRResolvedModelPackage.divisorialSheaf {m : ℕ} (σ : Fin m → NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase)
    (pos neg : Fin m → ℕ) (aplus aminus : X0MqComponents 𝔛reg.width → ℕ) : 𝔛reg.Y.Modules :=
  (List.finRange m).foldr (fun j N => ((σ j).1.ker ^ (pos j)).invModule ⊗ ((σ j).1.ker ^ (neg j)).module ⊗ N)
    ((∏ F, (𝔛reg.comp F) ^ (aplus F)).invModule ⊗ (∏ F, (𝔛reg.comp F) ^ (aminus F)).module)

p2m_export "ModularCurve.DRResolvedModelPackage" "divisorialSheaf"
end DRResolvedModelPackage

end ModularCurve

end

set_option autoImplicit false

p2m_open "CategoryTheory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso IsLocallyNoetherian IsOpenImmersion.lift Scheme.IdealSheafData.coe_support_ofIdealTop Scheme.IdealSheafData.support_comap isIso_iff_isOpenImmersion_and_surjective IsProper morphismRestrict_ι Scheme.IdealSheafData.comap_comp Scheme.Modules.pullback Scheme.Opens.range_ι Scheme.Hom Scheme.Pullback.range_map Scheme.IdealSheafData.top_mul morphismRestrictRestrict Scheme.homOfLE_apply' Scheme.Hom.image_preimage_eq_opensRange_inf Scheme.Hom.support_ker IsZariskiLocalAtTarget LocallyOfFiniteType Spec IsIntegral Spec.map Scheme IsOpenImmersion Scheme.Hom.comp_base Flat Scheme.zeroLocus_span isIntegral_of_isOpenImmersion IsClosedImmersion IsSeparated Scheme.mem_zeroLocus_iff Scheme.Hom.opensRange_of_isIso morphismRestrict_base Scheme.Modules.pullbackCongr IsOpenImmersion.isoOfRangeEq IsZariskiLocalAtTarget.of_iSup_eq_top Scheme.IdealSheafData.support_eq_bot_iff Scheme.Modules FormallyUnramified Scheme.Opens Scheme.homOfLE_ι Scheme.Hom.id_base Flat.generalizingMap morphismRestrictEq Scheme.Hom.comp_preimage Scheme.IdealSheafData.ofIdealTop IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Opens.opensRange_ι Scheme.Hom.comp_apply basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.Modules.pullbackComp IsOpenImmersion.isoOfRangeEq_hom_fac Scheme.ΓSpecIso Scheme.Hom.coe_opensRange Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule Scheme.Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app Scheme.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk Scheme.Hom.isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map Scheme.Modules.IsInvertible.isIso_ev_app_tensorUnit Scheme.Modules.nonempty_pullback_foldr_twist_iso Scheme.IdealSheafData.IsInvertible.comap_of_isOpenImmersion Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.ker_comp_of_isIso IdealSheafData.coe_support_ofIdealTop IdealSheafData.support_comap ringCatSheaf IdealSheafData.comap_comp Modules.pullback Opens.range_ι Hom mk Γ empty Pullback.range_map IdealSheafData.top_mul homOfLE_apply' Hom.image_preimage_eq_opensRange_inf Hom.support_ker Hom.comp_base zeroLocus_span mem_zeroLocus_iff Hom.opensRange_of_isIso basicOpen Modules.pullbackCongr mk.injEq IdealSheafData.support_eq_bot_iff Modules IdealSheafData.comap Opens homOfLE_ι Hom.id_base Hom.comp_preimage le_iff_specializes IdealSheafData.ofIdealTop Opens.opensRange_ι restrict Hom.comp_apply IdealSheafData Modules.pullbackComp ΓSpecIso Hom.coe_opensRange Modules.IsInvertible Modules.pullbackUnitIso IdealSheafData.IsInvertible IdealSheafData.module IdealSheafData.invModule Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk Hom.isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map Modules.IsInvertible.isIso_ev_app_tensorUnit Modules.nonempty_pullback_foldr_twist_iso IdealSheafData.IsInvertible.comap_of_isOpenImmersion Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "coe_support_ofIdealTop support_comap one_eq_top comap_comp mk map top_mul ker_fst_of_isClosedImmersion ideal support_eq_bot_iff comap ofIdealTop support mk.injEq IsInvertible isInvertible_top IsInvertible.mul module invModule IsInvertible.nonempty_mul_module_iso_tensor IsInvertible.nonempty_mul_invModule_iso_tensor IsInvertible.pow IsInvertible.isInvertible_module IsInvertible.comap_of_isOpenImmersion"
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {Z : Scheme.{u}}

theorem prod_pow_eq_prod_pow_of_forall_not_mem_range {ι : Type*} [Fintype ι] (C : ι → Z.IdealSheafData) (a : ι → ℕ)
    {k : ℕ} (r : Fin k → ι) (hr : Function.Injective r) (hfar : ∀ F, F ∉ Set.range r → C F = ⊤) :
    ∏ F, C F ^ a F = ∏ i : Fin k, C (r i) ^ a (r i) := by
  classical
  have h1 : ∏ F ∈ Finset.univ.image r, C F ^ a F = ∏ F, C F ^ a F := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro F _ hF
    have hF' : F ∉ Set.range r := by
      rintro ⟨i, rfl⟩
      exact hF (Finset.mem_image_of_mem r (Finset.mem_univ i))
    rw [hfar F hF', ← one_eq_top, one_pow]
  rw [← h1, Finset.prod_image fun i _ j _ h => hr h]

namespace TwistCalc

noncomputable def moduleTensorInvModuleIso {I : Z.IdealSheafData} (hI : I.IsInvertible) :
    I.module ⊗ I.invModule ≅ 𝟙_ Z.Modules :=
  (@asIso _ _ _ _ ((ihom.ev I.module).app (𝟙_ Z.Modules))
    (Scheme.Modules.IsInvertible.isIso_ev_app_tensorUnit (IsInvertible.isInvertible_module hI)) :
      I.module ⊗ I.invModule ≅ 𝟙_ Z.Modules)

noncomputable def mulModuleIso {I J : Z.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    (I * J).module ≅ I.module ⊗ J.module :=
  (IsInvertible.nonempty_mul_module_iso_tensor hI hJ).some

noncomputable def mulInvModuleIso {I J : Z.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    (I * J).invModule ≅ I.invModule ⊗ J.invModule :=
  (IsInvertible.nonempty_mul_invModule_iso_tensor hI hJ).some

noncomputable def shuffle (W X' Y Z' : Z.Modules) : (W ⊗ X') ⊗ (Y ⊗ Z') ≅ (W ⊗ Y) ⊗ (X' ⊗ Z') :=
  α_ W X' (Y ⊗ Z') ≪≫ whiskerLeftIso W ((α_ X' Y Z').symm ≪≫ whiskerRightIso (β_ X' Y) Z' ≪≫ α_ Y X' Z') ≪≫
    (α_ W Y (X' ⊗ Z')).symm

noncomputable def moduleTopIso : (⊤ : Z.IdealSheafData).module ≅ 𝟙_ Z.Modules :=
  let hT : (⊤ : Z.IdealSheafData).IsInvertible := isInvertible_top
  let U : Z.Modules := (⊤ : Z.IdealSheafData).module
  let e : U ≅ U ⊗ U :=
    eqToIso (congrArg Scheme.IdealSheafData.module (Scheme.IdealSheafData.top_mul (I := ⊤)).symm) ≪≫
      mulModuleIso hT hT
  (ρ_ U).symm ≪≫ whiskerLeftIso U (moduleTensorInvModuleIso hT).symm ≪≫ (α_ U U _).symm ≪≫
    whiskerRightIso e.symm _ ≪≫ moduleTensorInvModuleIso hT

noncomputable def invModuleTopIso : (⊤ : Z.IdealSheafData).invModule ≅ 𝟙_ Z.Modules :=
  (λ_ _).symm ≪≫ whiskerRightIso moduleTopIso.symm _ ≪≫ moduleTensorInvModuleIso isInvertible_top

theorem isInvertible_list_prod (l : List Z.IdealSheafData) (hl : ∀ I ∈ l, I.IsInvertible) : l.prod.IsInvertible := by
  induction l with
  | nil => exact isInvertible_top
  | cons a l ih =>
    rw [List.prod_cons]
    exact IsInvertible.mul (hl a (by simp)) (ih fun I hI => hl I (by simp [hI]))

noncomputable def splitIso {A A' B B' : Z.IdealSheafData}
    (hA : A.IsInvertible) (hA' : A'.IsInvertible) (hB : B.IsInvertible) (hB' : B'.IsInvertible) :
    (A * A').invModule ⊗ (B * B').module ≅ (A.invModule ⊗ B.module) ⊗ (A'.invModule ⊗ B'.module) :=
  (mulInvModuleIso hA hA' ⊗ᵢ mulModuleIso hB hB') ≪≫ shuffle _ _ _ _

theorem nonempty_foldr_list_iso_prod {m : ℕ} (K : Fin m → Z.IdealSheafData) (hK : ∀ j, (K j).IsInvertible)
    (pos neg : Fin m → ℕ) (M : Z.Modules) (l : List (Fin m)) :
    Nonempty (l.foldr (fun j N => (K j ^ pos j).invModule ⊗ (K j ^ neg j).module ⊗ N) M ≅
      (((l.map fun j => K j ^ pos j).prod).invModule ⊗ ((l.map fun j => K j ^ neg j).prod).module) ⊗ M) := by
  induction l with
  | nil =>
    exact ⟨(λ_ M).symm ≪≫ whiskerRightIso ((λ_ (𝟙_ Z.Modules)).symm ≪≫
      (invModuleTopIso.symm ⊗ᵢ moduleTopIso.symm)) M⟩
  | cons j l ih =>
    obtain ⟨e⟩ := ih
    have hP : ((l.map fun j => K j ^ pos j).prod).IsInvertible :=
      isInvertible_list_prod _ (by
        intro I hI; obtain ⟨k, -, rfl⟩ := List.mem_map.mp hI; exact IsInvertible.pow (hK k) _)
    have hQ : ((l.map fun j => K j ^ neg j).prod).IsInvertible :=
      isInvertible_list_prod _ (by
        intro I hI; obtain ⟨k, -, rfl⟩ := List.mem_map.mp hI; exact IsInvertible.pow (hK k) _)
    refine ⟨whiskerLeftIso _ (whiskerLeftIso _ e) ≪≫ (α_ _ _ _).symm ≪≫ (α_ _ _ M).symm ≪≫ whiskerRightIso
      (splitIso (IsInvertible.pow (hK j) (pos j)) hP (IsInvertible.pow (hK j) (neg j)) hQ).symm M ≪≫ ?_⟩
    simp only [List.map_cons, List.prod_cons]
    exact Iso.refl _

end TwistCalc

open TwistCalc

theorem nonempty_foldr_twist_iso_foldr_foldr_of_equiv {m m₁ m₂ : ℕ} (ε : Fin m₁ ⊕ Fin m₂ ≃ Fin m)
    (K : Fin m → Z.IdealSheafData) (hK : ∀ j, (K j).IsInvertible) (pos neg : Fin m → ℕ) (M : Z.Modules) :
    Nonempty ((List.finRange m).foldr (fun j N => (K j ^ pos j).invModule ⊗ (K j ^ neg j).module ⊗ N) M ≅
      (List.finRange m₁).foldr
        (fun i N => (K (ε (Sum.inl i)) ^ pos (ε (Sum.inl i))).invModule ⊗ (K (ε (Sum.inl i)) ^ neg (ε (Sum.inl i))).module ⊗ N)
        ((List.finRange m₂).foldr
          (fun i N => (K (ε (Sum.inr i)) ^ pos (ε (Sum.inr i))).invModule ⊗ (K (ε (Sum.inr i)) ^ neg (ε (Sum.inr i))).module ⊗ N)
          M)) := by
  classical

  obtain ⟨eL⟩ := nonempty_foldr_list_iso_prod K hK pos neg M (List.finRange m)
  obtain ⟨e₂⟩ := nonempty_foldr_list_iso_prod (fun i => K (ε (Sum.inr i))) (fun i => hK _)
    (fun i => pos (ε (Sum.inr i))) (fun i => neg (ε (Sum.inr i))) M (List.finRange m₂)
  obtain ⟨e₁⟩ := nonempty_foldr_list_iso_prod (fun i => K (ε (Sum.inl i))) (fun i => hK _)
    (fun i => pos (ε (Sum.inl i))) (fun i => neg (ε (Sum.inl i)))
    ((List.finRange m₂).foldr
      (fun i N => (K (ε (Sum.inr i)) ^ pos (ε (Sum.inr i))).invModule ⊗ (K (ε (Sum.inr i)) ^ neg (ε (Sum.inr i))).module ⊗ N) M)
    (List.finRange m₁)

  have hprod : ∀ a : Fin m → ℕ,
      ((List.finRange m₁).map fun i => K (ε (Sum.inl i)) ^ a (ε (Sum.inl i))).prod *
        ((List.finRange m₂).map fun i => K (ε (Sum.inr i)) ^ a (ε (Sum.inr i))).prod =
      ((List.finRange m).map fun j => K j ^ a j).prod := by
    intro a
    rw [← Fin.prod_univ_def, ← Fin.prod_univ_def, ← Fin.prod_univ_def,
      ← Fintype.prod_equiv ε (fun s => K (ε s) ^ a (ε s)) (fun j => K j ^ a j) (fun _ => rfl), Fintype.prod_sum_type]
  have h₁ : ∀ a : Fin m → ℕ, (((List.finRange m₁).map fun i => K (ε (Sum.inl i)) ^ a (ε (Sum.inl i))).prod).IsInvertible :=
    fun a => isInvertible_list_prod _ (by
      intro I hI; obtain ⟨k, -, rfl⟩ := List.mem_map.mp hI; exact IsInvertible.pow (hK _) _)
  have h₂ : ∀ a : Fin m → ℕ, (((List.finRange m₂).map fun i => K (ε (Sum.inr i)) ^ a (ε (Sum.inr i))).prod).IsInvertible :=
    fun a => isInvertible_list_prod _ (by
      intro I hI; obtain ⟨k, -, rfl⟩ := List.mem_map.mp hI; exact IsInvertible.pow (hK _) _)
  refine ⟨eL ≪≫ ?_ ≪≫ e₁.symm⟩
  refine ?_ ≪≫ whiskerLeftIso _ e₂.symm

  exact whiskerRightIso ((eqToIso (congrArg Scheme.IdealSheafData.invModule (hprod pos).symm) ⊗ᵢ
      eqToIso (congrArg Scheme.IdealSheafData.module (hprod neg).symm)) ≪≫
    splitIso (h₁ pos) (h₂ pos) (h₁ neg) (h₂ neg)) M ≪≫ α_ _ _ M

end AlgebraicGeometry.Scheme.IdealSheafData

set_option autoImplicit false

p2m_open "CategoryTheory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso IsLocallyNoetherian IsOpenImmersion.lift Scheme.IdealSheafData.coe_support_ofIdealTop Scheme.IdealSheafData.support_comap isIso_iff_isOpenImmersion_and_surjective IsProper morphismRestrict_ι Scheme.IdealSheafData.comap_comp Scheme.Modules.pullback Scheme.Opens.range_ι Scheme.Hom Scheme.Pullback.range_map Scheme.IdealSheafData.top_mul morphismRestrictRestrict Scheme.homOfLE_apply' Scheme.Hom.image_preimage_eq_opensRange_inf Scheme.Hom.support_ker IsZariskiLocalAtTarget LocallyOfFiniteType Spec IsIntegral Spec.map Scheme IsOpenImmersion Scheme.Hom.comp_base Flat Scheme.zeroLocus_span isIntegral_of_isOpenImmersion IsClosedImmersion IsSeparated Scheme.mem_zeroLocus_iff Scheme.Hom.opensRange_of_isIso morphismRestrict_base Scheme.Modules.pullbackCongr IsOpenImmersion.isoOfRangeEq IsZariskiLocalAtTarget.of_iSup_eq_top Scheme.IdealSheafData.support_eq_bot_iff Scheme.Modules FormallyUnramified Scheme.Opens Scheme.homOfLE_ι Scheme.Hom.id_base Flat.generalizingMap morphismRestrictEq Scheme.Hom.comp_preimage Scheme.IdealSheafData.ofIdealTop IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Opens.opensRange_ι Scheme.Hom.comp_apply basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.Modules.pullbackComp IsOpenImmersion.isoOfRangeEq_hom_fac Scheme.ΓSpecIso Scheme.Hom.coe_opensRange Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule Scheme.Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app Scheme.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk Scheme.Hom.isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map Scheme.Modules.IsInvertible.isIso_ev_app_tensorUnit Scheme.Modules.nonempty_pullback_foldr_twist_iso Scheme.IdealSheafData.IsInvertible.comap_of_isOpenImmersion Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.ker_comp_of_isIso IdealSheafData.coe_support_ofIdealTop IdealSheafData.support_comap ringCatSheaf IdealSheafData.comap_comp Modules.pullback Opens.range_ι Hom mk Γ empty Pullback.range_map IdealSheafData.top_mul homOfLE_apply' Hom.image_preimage_eq_opensRange_inf Hom.support_ker Hom.comp_base zeroLocus_span mem_zeroLocus_iff Hom.opensRange_of_isIso basicOpen Modules.pullbackCongr mk.injEq IdealSheafData.support_eq_bot_iff Modules IdealSheafData.comap Opens homOfLE_ι Hom.id_base Hom.comp_preimage le_iff_specializes IdealSheafData.ofIdealTop Opens.opensRange_ι restrict Hom.comp_apply IdealSheafData Modules.pullbackComp ΓSpecIso Hom.coe_opensRange Modules.IsInvertible Modules.pullbackUnitIso IdealSheafData.IsInvertible IdealSheafData.module IdealSheafData.invModule Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk Hom.isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map Modules.IsInvertible.isIso_ev_app_tensorUnit Modules.nonempty_pullback_foldr_twist_iso IdealSheafData.IsInvertible.comap_of_isOpenImmersion Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "coe_support_ofIdealTop support_comap one_eq_top comap_comp mk map top_mul ker_fst_of_isClosedImmersion ideal support_eq_bot_iff comap ofIdealTop support mk.injEq IsInvertible isInvertible_top IsInvertible.mul module invModule IsInvertible.nonempty_mul_module_iso_tensor IsInvertible.nonempty_mul_invModule_iso_tensor IsInvertible.pow IsInvertible.isInvertible_module IsInvertible.comap_of_isOpenImmersion"
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem comap_eq_top_of_forall_notMem_support {X Y : Scheme.{u}} (I : Y.IdealSheafData) (ψ : X ⟶ Y)
    (h : ∀ x : X, ψ.base x ∉ (I.support : Set Y)) : I.comap ψ = ⊤ := by
  rw [← support_eq_bot_iff, support_comap]
  ext x
  simp only [Closeds.coe_preimage, Set.mem_preimage, Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
  exact h x

theorem ker_comap_eq_ker_of_comp_eq {S X Y : Scheme.{u}} (ψ : X ⟶ Y) [IsOpenImmersion ψ] (σ : S ⟶ Y)
    [IsClosedImmersion σ] (σ' : S ⟶ X) (h : σ' ≫ ψ = σ) : σ.ker.comap ψ = σ'.ker := by

  have H : IsPullback σ' (𝟙 S) ψ σ := by
    refine IsOpenImmersion.isPullback σ' (𝟙 S) ψ σ (by rw [Category.id_comp, h]) ?_
    rw [Scheme.Hom.opensRange_of_isIso (𝟙 S)]
    apply top_le_iff.mp
    intro s _
    show σ.base s ∈ Set.range ψ.base
    exact ⟨σ'.base s, by rw [← Scheme.Hom.comp_apply, h]⟩
  rw [← ker_fst_of_isClosedImmersion σ ψ, ← H.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso IsLocallyNoetherian IsOpenImmersion.lift Scheme.IdealSheafData.coe_support_ofIdealTop Scheme.IdealSheafData.support_comap isIso_iff_isOpenImmersion_and_surjective IsProper morphismRestrict_ι Scheme.IdealSheafData.comap_comp Scheme.Modules.pullback Scheme.Opens.range_ι Scheme.Hom Scheme.Pullback.range_map Scheme.IdealSheafData.top_mul morphismRestrictRestrict Scheme.homOfLE_apply' Scheme.Hom.image_preimage_eq_opensRange_inf Scheme.Hom.support_ker IsZariskiLocalAtTarget LocallyOfFiniteType Spec IsIntegral Spec.map Scheme IsOpenImmersion Scheme.Hom.comp_base Flat Scheme.zeroLocus_span isIntegral_of_isOpenImmersion IsClosedImmersion IsSeparated Scheme.mem_zeroLocus_iff Scheme.Hom.opensRange_of_isIso morphismRestrict_base Scheme.Modules.pullbackCongr IsOpenImmersion.isoOfRangeEq IsZariskiLocalAtTarget.of_iSup_eq_top Scheme.IdealSheafData.support_eq_bot_iff Scheme.Modules FormallyUnramified Scheme.Opens Scheme.homOfLE_ι Scheme.Hom.id_base Flat.generalizingMap morphismRestrictEq Scheme.Hom.comp_preimage Scheme.IdealSheafData.ofIdealTop IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Opens.opensRange_ι Scheme.Hom.comp_apply basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.Modules.pullbackComp IsOpenImmersion.isoOfRangeEq_hom_fac Scheme.ΓSpecIso Scheme.Hom.coe_opensRange Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule Scheme.Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app Scheme.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk Scheme.Hom.isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map Scheme.Modules.IsInvertible.isIso_ev_app_tensorUnit Scheme.Modules.nonempty_pullback_foldr_twist_iso Scheme.IdealSheafData.IsInvertible.comap_of_isOpenImmersion Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.ker_comp_of_isIso IdealSheafData.coe_support_ofIdealTop IdealSheafData.support_comap ringCatSheaf IdealSheafData.comap_comp Modules.pullback Opens.range_ι Hom mk Γ empty Pullback.range_map IdealSheafData.top_mul homOfLE_apply' Hom.image_preimage_eq_opensRange_inf Hom.support_ker Hom.comp_base zeroLocus_span mem_zeroLocus_iff Hom.opensRange_of_isIso basicOpen Modules.pullbackCongr mk.injEq IdealSheafData.support_eq_bot_iff Modules IdealSheafData.comap Opens homOfLE_ι Hom.id_base Hom.comp_preimage le_iff_specializes IdealSheafData.ofIdealTop Opens.opensRange_ι restrict Hom.comp_apply IdealSheafData Modules.pullbackComp ΓSpecIso Hom.coe_opensRange Modules.IsInvertible Modules.pullbackUnitIso IdealSheafData.IsInvertible IdealSheafData.module IdealSheafData.invModule Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk Hom.isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map Modules.IsInvertible.isIso_ev_app_tensorUnit Modules.nonempty_pullback_foldr_twist_iso IdealSheafData.IsInvertible.comap_of_isOpenImmersion Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback presheaf Hom pullbackCongr restrict pullbackComp IsInvertible pullbackUnitIso IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app IsInvertible.isIso_ev_app_tensorUnit nonempty_pullback_foldr_twist_iso"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem nonempty_pullback_iso_unit_of_isOpenImmersion {X Y : Scheme.{u}} (ψ : X ⟶ Y) [IsOpenImmersion ψ]
    (L : Y.Modules) (W : Y.Opens) (hW : W ≤ ψ.opensRange)
    (h : Nonempty ((Scheme.Modules.pullback (ψ ⁻¹ᵁ W).ι).obj ((Scheme.Modules.pullback ψ).obj L) ≅
      SheafOfModules.unit (ψ ⁻¹ᵁ W).toScheme.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback W.ι).obj L ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) := by
  obtain ⟨τ⟩ := h

  haveI : IsIso (ψ ∣_ W) := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun y => ?_⟩⟩
    obtain ⟨x, hx⟩ := hW y.2
    refine ⟨⟨x, show ψ.base x ∈ W by rw [hx]; exact y.2⟩, Subtype.ext ?_⟩
    rw [morphismRestrict_base]
    exact hx
  let e : (ψ ⁻¹ᵁ W).toScheme ≅ W.toScheme := asIso (ψ ∣_ W)
  have hfac : e.inv ≫ (ψ ⁻¹ᵁ W).ι ≫ ψ = W.ι := by
    rw [← morphismRestrict_ι, ← Category.assoc]
    change (inv (ψ ∣_ W) ≫ (ψ ∣_ W)) ≫ W.ι = W.ι
    rw [IsIso.inv_hom_id, Category.id_comp]
  refine ⟨(Scheme.Modules.pullbackCongr hfac.symm).app L ≪≫ ((Scheme.Modules.pullbackComp _ _).app L).symm ≪≫
    (Scheme.Modules.pullback e.inv).mapIso (((Scheme.Modules.pullbackComp _ _).app L).symm ≪≫ τ) ≪≫
    Scheme.Modules.pullbackUnitIso e.inv⟩

end AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

p2m_open "CategoryTheory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.AlgebraicGeometry"

namespace CategoryTheory
p2m_export "CategoryTheory" "Category Iso.inv_hom_id_assoc MorphismProperty.isomorphisms eqToIso Category.comp_id ihom MorphismProperty Noetherian Injective inv over prod IsIso types Iso.refl pre Category.id_comp ihom.ev comp_apply MonoidalCategory sum IsPullback cancel_mono homOfLE Iso IsIso.inv_hom_id asIso Category.assoc"
namespace MonoidalCategory
p2m_export "CategoryTheory.MonoidalCategory" "mk whiskerLeftIso whiskerRightIso"
p2m_open "CategoryTheory.MonoidalCategory CategoryTheory"

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

noncomputable def foldrTensorAssocIso {ι : Type*} (A B : ι → C) (M : C) (l : List ι) :
    l.foldr (fun j N => (A j ⊗ B j) ⊗ N) M ≅ l.foldr (fun j N => A j ⊗ B j ⊗ N) M := by
  induction l with
  | nil => exact Iso.refl M
  | cons j l ih => exact whiskerLeftIso (A j ⊗ B j) ih ≪≫ α_ (A j) (B j) _

end CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso IsLocallyNoetherian IsOpenImmersion.lift Scheme.IdealSheafData.coe_support_ofIdealTop Scheme.IdealSheafData.support_comap isIso_iff_isOpenImmersion_and_surjective IsProper morphismRestrict_ι Scheme.IdealSheafData.comap_comp Scheme.Modules.pullback Scheme.Opens.range_ι Scheme.Hom Scheme.Pullback.range_map Scheme.IdealSheafData.top_mul morphismRestrictRestrict Scheme.homOfLE_apply' Scheme.Hom.image_preimage_eq_opensRange_inf Scheme.Hom.support_ker IsZariskiLocalAtTarget LocallyOfFiniteType Spec IsIntegral Spec.map Scheme IsOpenImmersion Scheme.Hom.comp_base Flat Scheme.zeroLocus_span isIntegral_of_isOpenImmersion IsClosedImmersion IsSeparated Scheme.mem_zeroLocus_iff Scheme.Hom.opensRange_of_isIso morphismRestrict_base Scheme.Modules.pullbackCongr IsOpenImmersion.isoOfRangeEq IsZariskiLocalAtTarget.of_iSup_eq_top Scheme.IdealSheafData.support_eq_bot_iff Scheme.Modules FormallyUnramified Scheme.Opens Scheme.homOfLE_ι Scheme.Hom.id_base Flat.generalizingMap morphismRestrictEq Scheme.Hom.comp_preimage Scheme.IdealSheafData.ofIdealTop IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Opens.opensRange_ι Scheme.Hom.comp_apply basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.Modules.pullbackComp IsOpenImmersion.isoOfRangeEq_hom_fac Scheme.ΓSpecIso Scheme.Hom.coe_opensRange Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule Scheme.Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app Scheme.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk Scheme.Hom.isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map Scheme.Modules.IsInvertible.isIso_ev_app_tensorUnit Scheme.Modules.nonempty_pullback_foldr_twist_iso Scheme.IdealSheafData.IsInvertible.comap_of_isOpenImmersion Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.ker_comp_of_isIso IdealSheafData.coe_support_ofIdealTop IdealSheafData.support_comap ringCatSheaf IdealSheafData.comap_comp Modules.pullback Opens.range_ι Hom mk Γ empty Pullback.range_map IdealSheafData.top_mul homOfLE_apply' Hom.image_preimage_eq_opensRange_inf Hom.support_ker Hom.comp_base zeroLocus_span mem_zeroLocus_iff Hom.opensRange_of_isIso basicOpen Modules.pullbackCongr mk.injEq IdealSheafData.support_eq_bot_iff Modules IdealSheafData.comap Opens homOfLE_ι Hom.id_base Hom.comp_preimage le_iff_specializes IdealSheafData.ofIdealTop Opens.opensRange_ι restrict Hom.comp_apply IdealSheafData Modules.pullbackComp ΓSpecIso Hom.coe_opensRange Modules.IsInvertible Modules.pullbackUnitIso IdealSheafData.IsInvertible IdealSheafData.module IdealSheafData.invModule Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk Hom.isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map Modules.IsInvertible.isIso_ev_app_tensorUnit Modules.nonempty_pullback_foldr_twist_iso IdealSheafData.IsInvertible.comap_of_isOpenImmersion Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "coe_support_ofIdealTop support_comap one_eq_top comap_comp mk map top_mul ker_fst_of_isClosedImmersion ideal support_eq_bot_iff comap ofIdealTop support mk.injEq IsInvertible isInvertible_top IsInvertible.mul module invModule IsInvertible.nonempty_mul_module_iso_tensor IsInvertible.nonempty_mul_invModule_iso_tensor IsInvertible.pow IsInvertible.isInvertible_module IsInvertible.comap_of_isOpenImmersion"
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {Z : Scheme.{u}}

theorem foldr_twist_congr {ι : Type*} (K K' : ι → Z.IdealSheafData) (h : ∀ j, K j = K' j) (pos neg : ι → ℕ)
    (M : Z.Modules) (l : List ι) :
    l.foldr (fun j N => (K j ^ pos j).invModule ⊗ (K j ^ neg j).module ⊗ N) M =
      l.foldr (fun j N => (K' j ^ pos j).invModule ⊗ (K' j ^ neg j).module ⊗ N) M := by
  have : K = K' := funext h
  subst this
  rfl

theorem foldr_twist_congr_left {ι : Type*} (K K' : ι → Z.IdealSheafData) (h : ∀ j, K j = K' j) (pos neg : ι → ℕ)
    (M : Z.Modules) (l : List ι) :
    l.foldr (fun j N => ((K j ^ pos j).invModule ⊗ (K j ^ neg j).module) ⊗ N) M =
      l.foldr (fun j N => ((K' j ^ pos j).invModule ⊗ (K' j ^ neg j).module) ⊗ N) M := by
  have : K = K' := funext h
  subst this
  rfl

end AlgebraicGeometry.Scheme.IdealSheafData

set_option autoImplicit false

p2m_open "CategoryTheory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso IsLocallyNoetherian IsOpenImmersion.lift Scheme.IdealSheafData.coe_support_ofIdealTop Scheme.IdealSheafData.support_comap isIso_iff_isOpenImmersion_and_surjective IsProper morphismRestrict_ι Scheme.IdealSheafData.comap_comp Scheme.Modules.pullback Scheme.Opens.range_ι Scheme.Hom Scheme.Pullback.range_map Scheme.IdealSheafData.top_mul morphismRestrictRestrict Scheme.homOfLE_apply' Scheme.Hom.image_preimage_eq_opensRange_inf Scheme.Hom.support_ker IsZariskiLocalAtTarget LocallyOfFiniteType Spec IsIntegral Spec.map Scheme IsOpenImmersion Scheme.Hom.comp_base Flat Scheme.zeroLocus_span isIntegral_of_isOpenImmersion IsClosedImmersion IsSeparated Scheme.mem_zeroLocus_iff Scheme.Hom.opensRange_of_isIso morphismRestrict_base Scheme.Modules.pullbackCongr IsOpenImmersion.isoOfRangeEq IsZariskiLocalAtTarget.of_iSup_eq_top Scheme.IdealSheafData.support_eq_bot_iff Scheme.Modules FormallyUnramified Scheme.Opens Scheme.homOfLE_ι Scheme.Hom.id_base Flat.generalizingMap morphismRestrictEq Scheme.Hom.comp_preimage Scheme.IdealSheafData.ofIdealTop IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Opens.opensRange_ι Scheme.Hom.comp_apply basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.Modules.pullbackComp IsOpenImmersion.isoOfRangeEq_hom_fac Scheme.ΓSpecIso Scheme.Hom.coe_opensRange Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule Scheme.Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app Scheme.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk Scheme.Hom.isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map Scheme.Modules.IsInvertible.isIso_ev_app_tensorUnit Scheme.Modules.nonempty_pullback_foldr_twist_iso Scheme.IdealSheafData.IsInvertible.comap_of_isOpenImmersion Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens"
p2m_open "AlgebraicGeometry"

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.ker_comp_of_isIso IdealSheafData.coe_support_ofIdealTop IdealSheafData.support_comap ringCatSheaf IdealSheafData.comap_comp Modules.pullback Opens.range_ι Hom mk Γ empty Pullback.range_map IdealSheafData.top_mul homOfLE_apply' Hom.image_preimage_eq_opensRange_inf Hom.support_ker Hom.comp_base zeroLocus_span mem_zeroLocus_iff Hom.opensRange_of_isIso basicOpen Modules.pullbackCongr mk.injEq IdealSheafData.support_eq_bot_iff Modules IdealSheafData.comap Opens homOfLE_ι Hom.id_base Hom.comp_preimage le_iff_specializes IdealSheafData.ofIdealTop Opens.opensRange_ι restrict Hom.comp_apply IdealSheafData Modules.pullbackComp ΓSpecIso Hom.coe_opensRange Modules.IsInvertible Modules.pullbackUnitIso IdealSheafData.IsInvertible IdealSheafData.module IdealSheafData.invModule Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk Hom.isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map Modules.IsInvertible.isIso_ev_app_tensorUnit Modules.nonempty_pullback_foldr_twist_iso IdealSheafData.IsInvertible.comap_of_isOpenImmersion Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens" namespace Hom p2m_export "AlgebraicGeometry.Scheme.Hom" "ker_comp_of_isIso image isOpenEmbedding id_app homeomorph app coe_preimage smoothLocus injective image_preimage_eq_opensRange_inf surjective support_ker mk comp_base preimage_mono opensRange_of_isIso comp_app mk.injEq isClosedMap cover continuous opensRange mem_preimage ker isClosedEmbedding id_base comp_preimage comp_apply coe_opensRange isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map isInvertible_ker_of_comp_eq_id_of_mem_opens" end Scheme.Hom
namespace Scheme.Hom
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

private theorem _root_.AlgebraicGeometry.Scheme.Hom.range_subset_of_closedPoint_mem {R : Type u} [CommRing R] [IsLocalRing R] {Y : Scheme.{u}}
    (s : Spec (CommRingCat.of R) ⟶ Y) (W : Y.Opens) (h : s.base (IsLocalRing.closedPoint R) ∈ W) :
    Set.range s.base ⊆ (W : Set Y) := by
  rintro _ ⟨t, rfl⟩
  have ht : t ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint t
  exact (ht.map s.base.hom.continuous).mem_open W.isOpen h

end Scheme.Hom
p2m_export "AlgebraicGeometry" "Scheme.Hom.range_subset_of_closedPoint_mem"
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

theorem Scheme.Hom.exists_lift_of_closedPoint_mem {R : Type u} [CommRing R] [IsLocalRing R] {Y : Scheme.{u}}
    (s : Spec (CommRingCat.of R) ⟶ Y) (W : Y.Opens) (h : s.base (IsLocalRing.closedPoint R) ∈ W) :
    ∃ s' : Spec (CommRingCat.of R) ⟶ W.toScheme, s' ≫ W.ι = s :=
  ⟨IsOpenImmersion.lift W.ι s (by rw [Scheme.Opens.range_ι]; exact s.range_subset_of_closedPoint_mem W h),
    IsOpenImmersion.lift_fac _ _ _⟩

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.ker_comp_of_isIso IdealSheafData.coe_support_ofIdealTop IdealSheafData.support_comap ringCatSheaf IdealSheafData.comap_comp Modules.pullback Opens.range_ι Hom mk Γ empty Pullback.range_map IdealSheafData.top_mul homOfLE_apply' Hom.image_preimage_eq_opensRange_inf Hom.support_ker Hom.comp_base zeroLocus_span mem_zeroLocus_iff Hom.opensRange_of_isIso basicOpen Modules.pullbackCongr mk.injEq IdealSheafData.support_eq_bot_iff Modules IdealSheafData.comap Opens homOfLE_ι Hom.id_base Hom.comp_preimage le_iff_specializes IdealSheafData.ofIdealTop Opens.opensRange_ι restrict Hom.comp_apply IdealSheafData Modules.pullbackComp ΓSpecIso Hom.coe_opensRange Modules.IsInvertible Modules.pullbackUnitIso IdealSheafData.IsInvertible IdealSheafData.module IdealSheafData.invModule Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk Hom.isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map Modules.IsInvertible.isIso_ev_app_tensorUnit Modules.nonempty_pullback_foldr_twist_iso IdealSheafData.IsInvertible.comap_of_isOpenImmersion Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens" namespace IdealSheafData p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "coe_support_ofIdealTop support_comap one_eq_top comap_comp mk map top_mul ker_fst_of_isClosedImmersion ideal support_eq_bot_iff comap ofIdealTop support mk.injEq IsInvertible isInvertible_top IsInvertible.mul module invModule IsInvertible.nonempty_mul_module_iso_tensor IsInvertible.nonempty_mul_invModule_iso_tensor IsInvertible.pow IsInvertible.isInvertible_module IsInvertible.comap_of_isOpenImmersion" end Scheme.IdealSheafData
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData" in

theorem Scheme.IdealSheafData.apply_ne_closedPoint_of_mem_support_comap_ker {R : Type u} [CommRing R] [IsLocalRing R]
    {Y Y' : Scheme.{u}} (π : Y ⟶ Spec (CommRingCat.of R)) (σ : Spec (CommRingCat.of R) ⟶ Y) [IsClosedImmersion σ]
    (hσ : σ ≫ π = 𝟙 _) (ψ : Y' ⟶ Y) (hfar : σ.base (IsLocalRing.closedPoint R) ∉ Set.range ψ.base)
    (y : Y') (hy : y ∈ ((σ.ker.comap ψ).support : Set Y')) :
    (ψ ≫ π).base y ≠ IsLocalRing.closedPoint R := by
  rw [Scheme.IdealSheafData.support_comap] at hy
  change ψ.base y ∈ (σ.ker.support : Set Y) at hy
  rw [Scheme.Hom.support_ker, σ.isClosedEmbedding.isClosed_range.closure_eq] at hy
  obtain ⟨t, ht⟩ := hy
  intro h
  have htt : t = IsLocalRing.closedPoint R := by
    have := congrArg (fun φ => φ.base t) hσ
    simp only [Scheme.Hom.comp_base, TopCat.comp_app, Scheme.Hom.id_base, TopCat.id_app] at this
    rw [← this, ht]
    simpa [Scheme.Hom.comp_base] using h
  subst htt
  exact hfar ⟨y, ht.symm⟩

theorem exists_open_subset_forall_notMem {X : Type u} [TopologicalSpace X] (U : Opens X) (x : X) (hx : x ∈ U)
    {ι : Type*} [Finite ι] (q : ι → X) (hq : ∀ i, IsClosed ({q i} : Set X)) (hne : ∀ i, q i ≠ x) :
    ∃ V : Opens X, x ∈ V ∧ V ≤ U ∧ ∀ i, q i ∉ V := by
  refine ⟨⟨(U : Set X) \ ⋃ i, {q i}, U.isOpen.sdiff (isClosed_iUnion_of_finite hq)⟩, ⟨hx, ?_⟩, fun y hy => hy.1, fun i hi => hi.2 ?_⟩
  · simp only [Set.mem_iUnion, Set.mem_singleton_iff, not_exists]
    exact fun i h => hne i h.symm
  · exact Set.mem_iUnion.mpr ⟨i, rfl⟩

end AlgebraicGeometry

set_option autoImplicit false

p2m_open "CategoryTheory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.AlgebraicGeometry TopologicalSpace MvPolynomial P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.MvPolynomial MvPolynomial.CrossingQuotient P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.MvPolynomial.CrossingQuotient ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRResolvedModelPackage.chainPos DRModel.baseChangeMap DRResolvedModelPackage DRModel DRModel.toBase DRModelPackage X0MqComponents x0MqAdj x0MqAdj_symm x0MqResolvedTable DRResolvedModelPackage.DRResolvedModelCharts"
namespace DRResolvedModelPackage
p2m_export "ModularCurve.DRResolvedModelPackage" "chainPos toBase toDR_iso_smoothLocus node toDR_over isIntegral node_fintype comp_isInvertible width mk.injEq mk Y nodeEquiv toDR_iso_generic regular node_deq edgePt smoothOffEdges exc_image flat isProper one_le_width edgePt_over comp toDR crossingPt DRResolvedModelCharts"
p2m_open "ModularCurve.DRResolvedModelPackage ModularCurve"

variable {p : ℕ} [Fact p.Prime] {𝔛 : DRModelPackage p} {O : Type} [CommRing O]
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
  (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ) {ϖ : O} {Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ϖ e).IdealSheafData}

namespace ChartWitness

variable {𝔛reg} (𝒞 : 𝔛reg.ChartWitness ϖ Fc)

private abbrev _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.ψ (n : 𝔛reg.node) : pullback (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)) ⟶ 𝔛reg.Y :=
  (𝒞.Φ n).hom ≫ (𝔛reg.toDR ⁻¹ᵁ 𝒞.U n).ι

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "ψ"
scoped instance (n : 𝔛reg.node) : IsOpenImmersion (𝒞.ψ n) := by
  dsimp [ψ]; infer_instance

private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.opensRange_ψ (n : 𝔛reg.node) : (𝒞.ψ n).opensRange = 𝔛reg.toDR ⁻¹ᵁ 𝒞.U n := by
  ext1
  simp only [Scheme.Hom.coe_opensRange, ψ, Scheme.Hom.comp_base, TopCat.coe_comp]
  rw [Set.range_comp, Set.range_eq_univ.mpr, Set.image_univ, Scheme.Opens.range_ι]
  exact (𝒞.Φ n).hom.homeomorph.surjective

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "opensRange_ψ"

private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.label_ψ (n : 𝔛reg.node) (d : Fin (𝔛reg.width n + 1)) :
    (𝔛reg.comp (DRResolvedModelPackage.chainPos 𝔛reg.width n d)).comap (𝒞.ψ n) =
      (Fc (𝔛reg.width n) d).comap (pullback.snd (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n))) := by
  rw [ψ, Scheme.IdealSheafData.comap_comp, 𝒞.label, ← Scheme.IdealSheafData.comap_comp, 𝒞.Φ_snd]

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "label_ψ"
private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.ψ_toDR (n : 𝔛reg.node) :
    𝒞.ψ n ≫ 𝔛reg.toDR = pullback.fst (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)) ≫ (𝒞.U n).ι := by
  rw [ψ, Category.assoc, ← morphismRestrict_ι, ← Category.assoc, 𝒞.Φ_fst]

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "ψ_toDR"
variable [IsDomain O] [IsDiscreteValuationRing O]

private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.farJ (n : 𝔛reg.node) (σ : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase)
    [IsClosedImmersion σ.1] (hK : (σ.1).ker.IsInvertible)
    (hfar : 𝔛reg.toDR.base ((σ.1).base (IsLocalRing.closedPoint O)) ∉ 𝒞.U n) :
    (((σ.1).ker).comap (𝒞.ψ n)).IsInvertible ∧
      ((((σ.1).ker).comap (𝒞.ψ n)).support : Set _) ∩
        (pullback.fst (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)) ≫ (𝒞.U n).ι ≫
          pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base ⁻¹' {IsLocalRing.closedPoint O} = ∅ := by
  refine ⟨Scheme.IdealSheafData.IsInvertible.comap_of_isOpenImmersion hK (𝒞.ψ n), ?_⟩
  have hfar' : (σ.1).base (IsLocalRing.closedPoint O) ∉ Set.range (𝒞.ψ n).base := by
    intro h
    have h' : (σ.1).base (IsLocalRing.closedPoint O) ∈ ((𝒞.ψ n).opensRange : Set 𝔛reg.Y) := h
    rw [𝒞.opensRange_ψ n] at h'
    exact hfar h'
  have hπ : 𝒞.ψ n ≫ 𝔛reg.toBase = pullback.fst (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)) ≫ (𝒞.U n).ι ≫
      pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) := by
    rw [← 𝔛reg.toDR_over, ← Category.assoc, 𝒞.ψ_toDR n, Category.assoc]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hy
  have := Scheme.IdealSheafData.apply_ne_closedPoint_of_mem_support_comap_ker 𝔛reg.toBase σ.1 σ.2 (𝒞.ψ n) hfar' y hy
  rwa [hπ] at this

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "farJ"
end ChartWitness
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness"

end ModularCurve.DRResolvedModelPackage
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"

set_option autoImplicit false

p2m_open "CategoryTheory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.AlgebraicGeometry TopologicalSpace MvPolynomial P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.MvPolynomial MvPolynomial.CrossingQuotient P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.MvPolynomial.CrossingQuotient ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve"

namespace CategoryTheory
p2m_export "CategoryTheory" "Category Iso.inv_hom_id_assoc MorphismProperty.isomorphisms eqToIso Category.comp_id ihom MorphismProperty Noetherian Injective inv over prod IsIso types Iso.refl pre Category.id_comp ihom.ev comp_apply MonoidalCategory sum IsPullback cancel_mono homOfLE Iso IsIso.inv_hom_id asIso Category.assoc"
namespace MonoidalCategory
p2m_export "CategoryTheory.MonoidalCategory" "mk whiskerLeftIso whiskerRightIso"
p2m_open "CategoryTheory.MonoidalCategory CategoryTheory"

variable {C : Type*} [Category C] [MonoidalCategory C]

noncomputable def foldrTensorBaseIso {ι : Type*} (A B : ι → C) {M M' : C} (e : M ≅ M') (l : List ι) :
    l.foldr (fun j N => A j ⊗ B j ⊗ N) M ≅ l.foldr (fun j N => A j ⊗ B j ⊗ N) M' := by
  induction l with
  | nil => exact e
  | cons j l ih => exact whiskerLeftIso (A j) (whiskerLeftIso (B j) ih)

end CategoryTheory.MonoidalCategory
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRResolvedModelPackage.chainPos DRModel.baseChangeMap DRResolvedModelPackage DRModel DRModel.toBase DRModelPackage X0MqComponents x0MqAdj x0MqAdj_symm x0MqResolvedTable DRResolvedModelPackage.DRResolvedModelCharts"
namespace DRResolvedModelPackage
p2m_export "ModularCurve.DRResolvedModelPackage" "chainPos toBase toDR_iso_smoothLocus node toDR_over isIntegral node_fintype comp_isInvertible width mk.injEq mk Y nodeEquiv toDR_iso_generic regular node_deq edgePt smoothOffEdges exc_image flat isProper one_le_width edgePt_over comp toDR crossingPt DRResolvedModelCharts"
namespace ChartWitness
p2m_open "ModularCurve.DRResolvedModelPackage ModularCurve"

variable {p : ℕ} [Fact p.Prime] {𝔛 : DRModelPackage p} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
  {𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ} {ϖ : O} {Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ϖ e).IdealSheafData}
  (𝒞 : 𝔛reg.ChartWitness ϖ Fc)

private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.nonempty_pullback_ψ_divisorialSheaf_iso (n : 𝔛reg.node)
    (ψ : pullback (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)) ⟶ 𝔛reg.Y) [IsOpenImmersion ψ]
    (hψ : ψ = (𝒞.Φ n).hom ≫ (𝔛reg.toDR ⁻¹ᵁ 𝒞.U n).ι)
    {m : ℕ} (σ : Fin m → NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase)
    [∀ j, IsClosedImmersion (σ j).1] (hK : ∀ j, ((σ j).1.ker).IsInvertible)
    (pos neg : Fin m → ℕ) (aplus aminus : X0MqComponents 𝔛reg.width → ℕ)
    {m₁ m₂ : ℕ} (ε : Fin m₁ ⊕ Fin m₂ ≃ Fin m)
    (σ' : Fin m₁ → (Spec (CommRingCat.of O) ⟶ pullback (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n))))
    (hσ' : ∀ i, σ' i ≫ ψ = (σ (ε (Sum.inl i))).1)
    (hinj : Function.Injective (fun d : Fin (𝔛reg.width n + 1) => DRResolvedModelPackage.chainPos 𝔛reg.width n d))
    (hfarC : ∀ F : X0MqComponents 𝔛reg.width, F ∉ Set.range (fun d : Fin (𝔛reg.width n + 1) =>
        DRResolvedModelPackage.chainPos 𝔛reg.width n d) → (𝔛reg.comp F).comap ψ = ⊤) :
    Nonempty ((Scheme.Modules.pullback ψ).obj (𝔛reg.divisorialSheaf σ pos neg aplus aminus) ≅
      (List.finRange m₁).foldr
        (fun i N => (((σ' i).ker ^ pos (ε (Sum.inl i))).invModule ⊗ ((σ' i).ker ^ neg (ε (Sum.inl i))).module) ⊗ N)
        ((List.finRange m₂).foldr
          (fun i N => (((((σ (ε (Sum.inr i))).1.ker).comap ψ) ^ pos (ε (Sum.inr i))).invModule ⊗
              ((((σ (ε (Sum.inr i))).1.ker).comap ψ) ^ neg (ε (Sum.inr i))).module) ⊗ N)
          ((∏ k : Fin (𝔛reg.width n + 1), (Fc (𝔛reg.width n) k).comap
                (pullback.snd (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n))) ^
                  aplus (DRResolvedModelPackage.chainPos 𝔛reg.width n k)).invModule ⊗
            (∏ k : Fin (𝔛reg.width n + 1), (Fc (𝔛reg.width n) k).comap
                (pullback.snd (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n))) ^
                  aminus (DRResolvedModelPackage.chainPos 𝔛reg.width n k)).module))) := by
  classical

  have hC : ∀ F, (𝔛reg.comp F).IsInvertible := 𝔛reg.comp_isInvertible
  have hK' : ∀ j, (((σ j).1.ker).comap ψ).IsInvertible := fun j =>
    Scheme.IdealSheafData.IsInvertible.comap_of_isOpenImmersion (hK j) ψ
  have hC' : ∀ F, ((𝔛reg.comp F).comap ψ).IsInvertible := fun F =>
    Scheme.IdealSheafData.IsInvertible.comap_of_isOpenImmersion (hC F) ψ
  obtain ⟨e1⟩ := Scheme.Modules.nonempty_pullback_foldr_twist_iso ψ (fun j => (σ j).1.ker) pos neg 𝔛reg.comp aplus aminus
    hK hC hK' hC'

  obtain ⟨e2⟩ := Scheme.IdealSheafData.nonempty_foldr_twist_iso_foldr_foldr_of_equiv ε (fun j => ((σ j).1.ker).comap ψ) hK'
    pos neg ((∏ F, (𝔛reg.comp F).comap ψ ^ aplus F).invModule ⊗ (∏ F, (𝔛reg.comp F).comap ψ ^ aminus F).module)

  have hvert : ∀ a : X0MqComponents 𝔛reg.width → ℕ,
      ∏ F, (𝔛reg.comp F).comap ψ ^ a F =
        ∏ k : Fin (𝔛reg.width n + 1), (Fc (𝔛reg.width n) k).comap
          (pullback.snd (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n))) ^ a (DRResolvedModelPackage.chainPos 𝔛reg.width n k) := by
    intro a
    rw [Scheme.IdealSheafData.prod_pow_eq_prod_pow_of_forall_not_mem_range (fun F => (𝔛reg.comp F).comap ψ) a _ hinj hfarC]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hψ, 𝒞.label_ψ n k]

  have hnear : ∀ i, ((σ (ε (Sum.inl i))).1.ker).comap ψ = (σ' i).ker := fun i =>
    Scheme.IdealSheafData.ker_comap_eq_ker_of_comp_eq ψ (σ (ε (Sum.inl i))).1 (σ' i) (hσ' i)
  refine ⟨e1 ≪≫ e2 ≪≫ ?_⟩

  rw [Scheme.IdealSheafData.foldr_twist_congr (fun i => ((σ (ε (Sum.inl i))).1.ker).comap ψ) (fun i => (σ' i).ker) hnear]

  refine foldrTensorBaseIso _ _ ?_ (List.finRange m₁) ≪≫ (foldrTensorAssocIso _ _ _ _).symm

  exact foldrTensorBaseIso _ _
      (eqToIso (congrArg₂ (fun P Q : (pullback (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n))).IdealSheafData =>
        P.invModule ⊗ Q.module) (hvert aplus) (hvert aminus))) (List.finRange m₂) ≪≫
    (foldrTensorAssocIso _ _ _ _).symm

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "nonempty_pullback_ψ_divisorialSheaf_iso"
end ModularCurve.DRResolvedModelPackage.ChartWitness
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"

end
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"

set_option autoImplicit false

p2m_open "CategoryTheory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.AlgebraicGeometry TopologicalSpace MvPolynomial P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.MvPolynomial MvPolynomial.CrossingQuotient P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.MvPolynomial.CrossingQuotient ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRResolvedModelPackage.chainPos DRModel.baseChangeMap DRResolvedModelPackage DRModel DRModel.toBase DRModelPackage X0MqComponents x0MqAdj x0MqAdj_symm x0MqResolvedTable DRResolvedModelPackage.DRResolvedModelCharts"
namespace DRResolvedModelPackage
p2m_export "ModularCurve.DRResolvedModelPackage" "chainPos toBase toDR_iso_smoothLocus node toDR_over isIntegral node_fintype comp_isInvertible width mk.injEq mk Y nodeEquiv toDR_iso_generic regular node_deq edgePt smoothOffEdges exc_image flat isProper one_le_width edgePt_over comp toDR crossingPt DRResolvedModelCharts"
p2m_open "ModularCurve.DRResolvedModelPackage ModularCurve"

variable {p : ℕ} [Fact p.Prime] {𝔛 : DRModelPackage p} {O : Type} [CommRing O]
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
  (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ) {ϖ : O} {Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ϖ e).IdealSheafData}

namespace ChartWitness

variable {𝔛reg} (𝒞 : 𝔛reg.ChartWitness ϖ Fc) (V : 𝔛reg.node → (DRModelPackage.XO p O).Opens)
  (hV : ∀ n, V n ≤ 𝒞.U n)

private def _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.restrictF (n : 𝔛reg.node) : (V n).toScheme ⟶ crossingScheme (ϖ ^ 𝔛reg.width n) :=
  (DRModelPackage.XO p O).homOfLE (hV n) ≫ 𝒞.f n

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "restrictF"

private def _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.restrictMap (n : 𝔛reg.node) :
    pullback (𝒞.restrictF V hV n) (Resolution.toCrossing ϖ (𝔛reg.width n)) ⟶
      pullback (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)) :=
  pullback.map _ _ _ _ ((DRModelPackage.XO p O).homOfLE (hV n)) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id]; rfl) (by rw [Category.comp_id, Category.id_comp])

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "restrictMap"
scoped instance (n : 𝔛reg.node) : IsOpenImmersion (𝒞.restrictMap V hV n) := by
  unfold restrictMap; infer_instance

@[reassoc]
private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.restrictMap_fst (n : 𝔛reg.node) :
    𝒞.restrictMap V hV n ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (DRModelPackage.XO p O).homOfLE (hV n) :=
  pullback.lift_fst _ _ _

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "restrictMap_fst restrictMap_fst_assoc"
@[reassoc]
private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.restrictMap_snd (n : 𝔛reg.node) :
    𝒞.restrictMap V hV n ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [← Category.comp_id (pullback.snd (𝒞.restrictF V hV n) _)]
  exact pullback.lift_snd _ _ _

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "restrictMap_snd restrictMap_snd_assoc"

private def _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.restrictEmb (n : 𝔛reg.node) :
    pullback (𝒞.restrictF V hV n) (Resolution.toCrossing ϖ (𝔛reg.width n)) ⟶ 𝔛reg.Y :=
  𝒞.restrictMap V hV n ≫ (𝒞.Φ n).hom ≫ (𝔛reg.toDR ⁻¹ᵁ (𝒞.U n)).ι

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "restrictEmb"
scoped instance (n : 𝔛reg.node) : IsOpenImmersion (𝒞.restrictEmb V hV n) := by
  unfold restrictEmb; infer_instance

private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.toDR_Φ_ι_apply (n : 𝔛reg.node) (z : ↥(pullback (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)))) :
    𝔛reg.toDR.base (((𝒞.Φ n).hom ≫ (𝔛reg.toDR ⁻¹ᵁ (𝒞.U n)).ι).base z) =
      (𝒞.U n).ι.base ((pullback.fst (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n))).base z) := by
  have h : ((𝒞.Φ n).hom ≫ (𝔛reg.toDR ⁻¹ᵁ (𝒞.U n)).ι) ≫ 𝔛reg.toDR
      = pullback.fst (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)) ≫ (𝒞.U n).ι := by
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, 𝒞.Φ_fst n]
  rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "toDR_Φ_ι_apply"
private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.range_restrictEmb (n : 𝔛reg.node) :
    Set.range (𝒞.restrictEmb V hV n).base = Set.range (𝔛reg.toDR ⁻¹ᵁ (V n)).ι.base := by
  rw [Scheme.Opens.range_ι]

  have hj : Set.range ((DRModelPackage.XO p O).homOfLE (hV n)).base = (𝒞.U n).ι.base ⁻¹' (V n : Set _) := by
    ext u
    constructor
    · rintro ⟨v, rfl⟩
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
      exact v.2
    · intro hu
      exact ⟨⟨u.1, hu⟩, Subtype.ext (by rw [Scheme.homOfLE_apply'])⟩
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    change 𝔛reg.toDR.base (((𝒞.Φ n).hom ≫ (𝔛reg.toDR ⁻¹ᵁ (𝒞.U n)).ι).base ((𝒞.restrictMap V hV n).base z)) ∈ V n
    have hz : (pullback.fst (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n))).base ((𝒞.restrictMap V hV n).base z)
        = ((DRModelPackage.XO p O).homOfLE (hV n)).base
            ((pullback.fst (𝒞.restrictF V hV n) (Resolution.toCrossing ϖ (𝔛reg.width n))).base z) := by
      rw [← Scheme.Hom.comp_apply, restrictMap_fst, Scheme.Hom.comp_apply]
    rw [toDR_Φ_ι_apply, hz, ← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    exact ((pullback.fst (𝒞.restrictF V hV n) (Resolution.toCrossing ϖ (𝔛reg.width n))).base z).2
  · intro y hy

    have hyU : y ∈ 𝔛reg.toDR ⁻¹ᵁ (𝒞.U n) := hV n hy
    obtain ⟨w, rfl⟩ : ∃ w, ((𝒞.Φ n).hom ≫ (𝔛reg.toDR ⁻¹ᵁ (𝒞.U n)).ι).base w = y :=
      ⟨(𝒞.Φ n).inv.base ⟨y, hyU⟩, by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]; rfl⟩

    have hw : w ∈ Set.range (𝒞.restrictMap V hV n).base := by
      rw [restrictMap, Scheme.Pullback.range_map]
      refine ⟨?_, by simp⟩
      rw [Set.mem_preimage, hj, Set.mem_preimage]
      change 𝔛reg.toDR.base _ ∈ V n at hy
      rwa [toDR_Φ_ι_apply] at hy
    obtain ⟨z, rfl⟩ := hw
    exact ⟨z, rfl⟩

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "range_restrictEmb"

private def _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.restrictΦ (n : 𝔛reg.node) :
    pullback (𝒞.restrictF V hV n) (Resolution.toCrossing ϖ (𝔛reg.width n)) ≅ (𝔛reg.toDR ⁻¹ᵁ (V n)).toScheme :=
  IsOpenImmersion.isoOfRangeEq (𝒞.restrictEmb V hV n) (𝔛reg.toDR ⁻¹ᵁ (V n)).ι (𝒞.range_restrictEmb V hV n)

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "restrictΦ"
@[reassoc]
private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.restrictΦ_hom_ι (n : 𝔛reg.node) :
    (𝒞.restrictΦ V hV n).hom ≫ (𝔛reg.toDR ⁻¹ᵁ (V n)).ι =
      𝒞.restrictMap V hV n ≫ (𝒞.Φ n).hom ≫ (𝔛reg.toDR ⁻¹ᵁ (𝒞.U n)).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "restrictΦ_hom_ι restrictΦ_hom_ι_assoc"
include hV in
private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.preimage_mono (n : 𝔛reg.node) : 𝔛reg.toDR ⁻¹ᵁ (V n) ≤ 𝔛reg.toDR ⁻¹ᵁ (𝒞.U n) :=
  fun _ hy => hV n hy

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "preimage_mono"

private def _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.restrictG (n : 𝔛reg.node) : (𝔛reg.toDR ⁻¹ᵁ (V n)).toScheme ⟶ Resolution ϖ (𝔛reg.width n) :=
  𝔛reg.Y.homOfLE (𝒞.preimage_mono V hV n) ≫ 𝒞.g n

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "restrictG"
@[reassoc]
private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.restrictΦ_hom_homOfLE (n : 𝔛reg.node) :
    (𝒞.restrictΦ V hV n).hom ≫ 𝔛reg.Y.homOfLE (𝒞.preimage_mono V hV n) =
      𝒞.restrictMap V hV n ≫ (𝒞.Φ n).hom := by
  rw [← cancel_mono (𝔛reg.toDR ⁻¹ᵁ (𝒞.U n)).ι, Category.assoc, Scheme.homOfLE_ι, restrictΦ_hom_ι,
    Category.assoc]

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "restrictΦ_hom_homOfLE restrictΦ_hom_homOfLE_assoc"
variable [IsDomain O] [IsDiscreteValuationRing O]

private def _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.restrict (hxV : ∀ n, 𝔛reg.crossingPt n ∈ V n) : 𝔛reg.ChartWitness ϖ Fc where
  U := V
  mem_U := hxV
  not_mem_U n m hmn h := 𝒞.not_mem_U n m hmn (hV n h)
  f := 𝒞.restrictF V hV
  etale n := by unfold restrictF; infer_instance
  f_over n := by
    rw [restrictF, Category.assoc, 𝒞.f_over, ← Category.assoc, Scheme.homOfLE_ι]
  f_mem_Vc_iff n y := by
    rw [restrictF, Scheme.Hom.comp_apply, 𝒞.f_mem_Vc_iff]
    have : (((DRModelPackage.XO p O).homOfLE (hV n)).base y).1 = y.1 := by
      have := congrArg Subtype.val (Scheme.homOfLE_apply' (hV n) y.1 y.2)
      simpa only [Subtype.coe_eta] using this
    rw [this]
  hinj n y y' h1 h2 h3 := by
    apply (𝒞.restrictMap V hV n).isOpenEmbedding.injective
    apply 𝒞.hinj n
    · rw [← Scheme.Hom.comp_apply, restrictMap_fst, Scheme.Hom.comp_apply]
      have := congrArg Subtype.val (Scheme.homOfLE_apply' (hV n) _
        ((pullback.fst (𝒞.restrictF V hV n) (Resolution.toCrossing ϖ (𝔛reg.width n))).base y).2)
      simp only [Subtype.coe_eta] at this
      rw [this]; exact h1
    · rw [← Scheme.Hom.comp_apply, restrictMap_fst, Scheme.Hom.comp_apply]
      have := congrArg Subtype.val (Scheme.homOfLE_apply' (hV n) _
        ((pullback.fst (𝒞.restrictF V hV n) (Resolution.toCrossing ϖ (𝔛reg.width n))).base y').2)
      simp only [Subtype.coe_eta] at this
      rw [this]; exact h2
    · rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, restrictMap_snd]
      exact h3
  g := 𝒞.restrictG V hV
  Φ := 𝒞.restrictΦ V hV
  Φ_fst n := by
    rw [← cancel_mono (V n).ι, Category.assoc, morphismRestrict_ι, restrictΦ_hom_ι_assoc,
      ← morphismRestrict_ι, ← Category.assoc (𝒞.Φ n).hom, 𝒞.Φ_fst, restrictMap_fst_assoc, Scheme.homOfLE_ι]
  Φ_snd n := by
    rw [restrictG, restrictΦ_hom_homOfLE_assoc, 𝒞.Φ_snd, restrictMap_snd]
  label n d := by
    rw [restrictG, Scheme.IdealSheafData.comap_comp, ← 𝒞.label n d, ← Scheme.IdealSheafData.comap_comp,
      Scheme.homOfLE_ι]

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "restrict"
omit [IsDomain O] [IsDiscreteValuationRing O] in
@[scoped simp] private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.restrict_U (hxV : ∀ n, 𝔛reg.crossingPt n ∈ V n) : (𝒞.restrict V hV hxV).U = V := rfl

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "restrict_U"
omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.restrict_f (hxV : ∀ n, 𝔛reg.crossingPt n ∈ V n) (n : 𝔛reg.node) :
    (𝒞.restrict V hV hxV).f n = (DRModelPackage.XO p O).homOfLE (hV n) ≫ 𝒞.f n := rfl

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "restrict_f"
omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.restrict_g (hxV : ∀ n, 𝔛reg.crossingPt n ∈ V n) (n : 𝔛reg.node) :
    (𝒞.restrict V hV hxV).g n = 𝔛reg.Y.homOfLE (𝒞.preimage_mono V hV n) ≫ 𝒞.g n := rfl

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "restrict_g"
omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.restrict_Φ_hom_ι (hxV : ∀ n, 𝔛reg.crossingPt n ∈ V n) (n : 𝔛reg.node) :
    ((𝒞.restrict V hV hxV).Φ n).hom ≫ (𝔛reg.toDR ⁻¹ᵁ (V n)).ι =
      𝒞.restrictMap V hV n ≫ (𝒞.Φ n).hom ≫ (𝔛reg.toDR ⁻¹ᵁ (𝒞.U n)).ι :=
  𝒞.restrictΦ_hom_ι V hV n

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "restrict_Φ_hom_ι"
omit [IsDomain O] [IsDiscreteValuationRing O] in

private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.chainPos_eq_inr (n : 𝔛reg.node) (i : Fin (𝔛reg.width n - 1)) :
    DRResolvedModelPackage.chainPos 𝔛reg.width n ((i : ℕ) + 1) = Sum.inr ⟨n, i⟩ := by
  unfold DRResolvedModelPackage.chainPos
  have h1 : (i : ℕ) + 1 ≠ 0 := Nat.succ_ne_zero _
  have h2 : (i : ℕ) + 1 < 𝔛reg.width n := by have := i.2; omega
  rw [dif_neg h1, dif_pos h2]
  congr

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "chainPos_eq_inr"
omit [IsDomain O] [IsDiscreteValuationRing O] in

private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.chainPos_eq_inr_iff (n : 𝔛reg.node) (i : Fin (𝔛reg.width n - 1)) (k : ℕ) :
    DRResolvedModelPackage.chainPos 𝔛reg.width n k = Sum.inr ⟨n, i⟩ ↔ k = (i : ℕ) + 1 := by
  have hi := i.2
  unfold DRResolvedModelPackage.chainPos
  split_ifs with h0 hlt
  · simp only [false_iff]; omega
  · simp only [Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, true_and, Fin.ext_iff]; omega
  · simp only [false_iff]; omega

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "chainPos_eq_inr_iff"

private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.exists_sectionLift (n : 𝔛reg.node) (σ : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase)
    (i : Fin (𝔛reg.width n - 1))
    (hσ : (σ.1).base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp (Sum.inr ⟨n, i⟩)).support ∧
      ∀ w, w ≠ Sum.inr ⟨n, i⟩ → (σ.1).base (IsLocalRing.closedPoint O) ∉ (𝔛reg.comp w).support) :
    ∃ σ' : Spec (CommRingCat.of O) ⟶ pullback (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)),
      σ' ≫ ((𝒞.Φ n).hom ≫ (𝔛reg.toDR ⁻¹ᵁ 𝒞.U n).ι) = σ.1 ∧
      σ' ≫ pullback.fst (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)) ≫ (𝒞.U n).ι ≫
          pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) = 𝟙 _ ∧
      (σ'.base (IsLocalRing.closedPoint O) ∈
          ((Fc (𝔛reg.width n) ⟨(i : ℕ) + 1, by omega⟩).comap
            (pullback.snd (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)))).support ∧
        ∀ k : Fin (𝔛reg.width n + 1), (k : ℕ) ≠ (i : ℕ) + 1 →
          σ'.base (IsLocalRing.closedPoint O) ∉
            ((Fc (𝔛reg.width n) k).comap (pullback.snd (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)))).support) := by
  obtain ⟨hmem, hnot⟩ := hσ
  set y₀ := σ.1.base (IsLocalRing.closedPoint O) with hy₀

  have hyU : y₀ ∈ 𝔛reg.toDR ⁻¹ᵁ (𝒞.U n) := by
    change 𝔛reg.toDR.base y₀ ∈ 𝒞.U n
    rw [𝔛reg.exc_image n i y₀ hmem]
    exact 𝒞.mem_U n

  have hrange : Set.range σ.1.base ⊆ Set.range (𝔛reg.toDR ⁻¹ᵁ (𝒞.U n)).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint t).map σ.1.base.hom.continuous).mem_open
      (𝔛reg.toDR ⁻¹ᵁ (𝒞.U n)).isOpen hyU
  let s' : Spec (CommRingCat.of O) ⟶ (𝔛reg.toDR ⁻¹ᵁ (𝒞.U n)).toScheme :=
    IsOpenImmersion.lift (𝔛reg.toDR ⁻¹ᵁ (𝒞.U n)).ι σ.1 hrange
  have hs' : s' ≫ (𝔛reg.toDR ⁻¹ᵁ (𝒞.U n)).ι = σ.1 := IsOpenImmersion.lift_fac _ _ _
  refine ⟨s' ≫ (𝒞.Φ n).inv, ?_, ?_, ?_⟩
  · rw [Category.assoc, Iso.inv_hom_id_assoc, hs']
  · have h1 : (s' ≫ (𝒞.Φ n).inv) ≫ pullback.fst (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)) =
        s' ≫ (𝔛reg.toDR ∣_ 𝒞.U n) := by
      rw [← 𝒞.Φ_fst n, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, h1, Category.assoc, ← Category.assoc (𝔛reg.toDR ∣_ 𝒞.U n), morphismRestrict_ι,
      Category.assoc, 𝔛reg.toDR_over, ← Category.assoc, hs']
    exact σ.2
  ·
    have hbase : ((s' ≫ (𝒞.Φ n).inv) ≫ (𝒞.Φ n).hom ≫ (𝔛reg.toDR ⁻¹ᵁ (𝒞.U n)).ι).base (IsLocalRing.closedPoint O) = y₀ := by
      rw [Category.assoc, Iso.inv_hom_id_assoc, hs']
    have hlab : ∀ d : Fin (𝔛reg.width n + 1),
        (Fc (𝔛reg.width n) d).comap (pullback.snd (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n))) =
          (𝔛reg.comp (DRResolvedModelPackage.chainPos 𝔛reg.width n d)).comap
            ((𝒞.Φ n).hom ≫ (𝔛reg.toDR ⁻¹ᵁ (𝒞.U n)).ι) := by
      intro d
      rw [Scheme.IdealSheafData.comap_comp, 𝒞.label n d, ← Scheme.IdealSheafData.comap_comp, 𝒞.Φ_snd]
    have key : ∀ d : Fin (𝔛reg.width n + 1),
        (s' ≫ (𝒞.Φ n).inv).base (IsLocalRing.closedPoint O) ∈
            ((Fc (𝔛reg.width n) d).comap (pullback.snd (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)))).support ↔
          y₀ ∈ (𝔛reg.comp (DRResolvedModelPackage.chainPos 𝔛reg.width n d)).support := by
      intro d
      rw [hlab d, Scheme.IdealSheafData.support_comap]
      rw [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage,
        ← Scheme.Hom.comp_apply, hbase, SetLike.mem_coe]
    refine ⟨(key _).mpr ?_, fun k hk h => ?_⟩
    · have := chainPos_eq_inr n i
      simp only at this ⊢
      rw [this]; exact hmem
    · have h' := (key k).mp h
      exact hnot _ (fun heq => hk ((chainPos_eq_inr_iff n i k).mp heq)) h'

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "exists_sectionLift"
end ChartWitness
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"

end ModularCurve.DRResolvedModelPackage
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"

end
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"

set_option autoImplicit false

p2m_open "MazurRapoportAppendix ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "DRResolvedModelPackage.chainPos DRModel.baseChangeMap DRResolvedModelPackage DRModel DRModel.toBase DRModelPackage X0MqComponents x0MqAdj x0MqAdj_symm x0MqResolvedTable DRResolvedModelPackage.DRResolvedModelCharts"
p2m_open "ModularCurve"

variable {node : Type} [Fintype node] [DecidableEq node] (width : node → ℕ)

omit [Fintype node] [DecidableEq node] in
theorem chainPos_zero (n : node) : DRResolvedModelPackage.chainPos width n 0 = Sum.inl 0 := by
  simp [DRResolvedModelPackage.chainPos]

omit [Fintype node] [DecidableEq node] in
theorem chainPos_of_pos_of_lt (n : node) (d : ℕ) (h0 : d ≠ 0) (hd : d < width n) :
    DRResolvedModelPackage.chainPos width n d = Sum.inr ⟨n, ⟨d - 1, by omega⟩⟩ := by
  simp [DRResolvedModelPackage.chainPos, h0, hd]

omit [Fintype node] [DecidableEq node] in
theorem chainPos_of_le (n : node) (d : ℕ) (h0 : d ≠ 0) (hd : width n ≤ d) :
    DRResolvedModelPackage.chainPos width n d = Sum.inl 1 := by
  simp [DRResolvedModelPackage.chainPos, h0, not_lt.mpr hd]

theorem x0MqAdj_inr_eq (n : node) (i : Fin (width n - 1)) (F : X0MqComponents width) :
    x0MqAdj width F (Sum.inr ⟨n, i⟩) =
      (if F = DRResolvedModelPackage.chainPos width n i then 1 else 0) +
        (if F = DRResolvedModelPackage.chainPos width n (i + 2) then 1 else 0) := by
  have hi := i.isLt

  have hL : DRResolvedModelPackage.chainPos width n i =
      if (i : ℕ) = 0 then Sum.inl 0 else Sum.inr ⟨n, ⟨(i : ℕ) - 1, by omega⟩⟩ := by
    split_ifs with h
    · rw [h, chainPos_zero]
    · exact chainPos_of_pos_of_lt width n i h (by omega)

  have hR : DRResolvedModelPackage.chainPos width n (i + 2) =
      if h : (i : ℕ) + 2 < width n then Sum.inr ⟨n, ⟨(i : ℕ) + 1, by omega⟩⟩ else Sum.inl 1 := by
    split_ifs with h
    · exact chainPos_of_pos_of_lt width n (i + 2) (by omega) h
    · exact chainPos_of_le width n (i + 2) (by omega) (not_lt.mp h)
  rw [hL, hR]
  rcases F with j | ⟨n', k⟩
  · fin_cases j <;> (simp only [x0MqAdj]; split_ifs <;> simp_all <;> omega)
  · by_cases hn : n' = n
    · subst hn
      simp only [x0MqAdj]
      split_ifs <;> simp_all [Fin.ext_iff] <;> omega
    · have h1 : ¬ (n' = n ∧ ((k : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (k : ℕ))) := fun h => hn h.1
      simp only [x0MqAdj, if_neg h1]
      split_ifs <;> simp_all

theorem sum_mul_x0MqAdj_inr (c : X0MqComponents width → ℤ) (n : node) (i : Fin (width n - 1)) :
    ∑ F, c F * (x0MqAdj width F (Sum.inr ⟨n, i⟩) : ℤ) =
      c (DRResolvedModelPackage.chainPos width n i) + c (DRResolvedModelPackage.chainPos width n (i + 2)) := by
  simp only [x0MqAdj_inr_eq, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_add, mul_ite, mul_one,
    mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sum_x0MqAdj_inr (n : node) (i : Fin (width n - 1)) :
    ∑ F, (x0MqAdj width (Sum.inr ⟨n, i⟩) F : ℤ) = 2 := by
  have h := sum_mul_x0MqAdj_inr width (fun _ => 1) n i
  simp only [one_mul] at h
  rw [Finset.sum_congr rfl fun F _ => by rw [x0MqAdj_symm], h]
  norm_num

theorem intersectionAlpha_x0MqResolvedTable_inr (c : X0MqComponents width → ℤ) (n : node) (i : Fin (width n - 1)) :
    intersectionAlpha (x0MqResolvedTable width) c (Sum.inr ⟨n, i⟩) =
      c (DRResolvedModelPackage.chainPos width n i) - 2 * c (Sum.inr ⟨n, i⟩) +
        c (DRResolvedModelPackage.chainPos width n (i + 2)) := by
  rw [intersectionAlpha_apply]
  have hsplit : ∀ F, c F * (x0MqResolvedTable width).inter F (Sum.inr ⟨n, i⟩) =
      c F * (x0MqAdj width F (Sum.inr ⟨n, i⟩) : ℤ) -
        (if F = Sum.inr ⟨n, i⟩ then c F * ∑ j', (x0MqAdj width F j' : ℤ) else 0) := by
    intro F
    simp only [x0MqResolvedTable]
    split_ifs with h
    · subst h; ring
    · ring
  have key : (∑ F, if F = Sum.inr ⟨n, i⟩ then c F * ∑ j', (x0MqAdj width F j' : ℤ) else 0) =
      c (Sum.inr ⟨n, i⟩) * ∑ j', (x0MqAdj width (Sum.inr ⟨n, i⟩) j' : ℤ) := by
    rw [Fintype.sum_eq_single (Sum.inr ⟨n, i⟩ : X0MqComponents width) (fun F hF => if_neg hF), if_pos rfl]
  rw [Finset.sum_congr rfl fun F _ => hsplit F, Finset.sum_sub_distrib, sum_mul_x0MqAdj_inr, key, sum_x0MqAdj_inr]
  ring

namespace DRResolvedModelPackage p2m_export "ModularCurve.DRResolvedModelPackage" "chainPos toBase toDR_iso_smoothLocus node toDR_over isIntegral node_fintype comp_isInvertible width mk.injEq mk Y nodeEquiv toDR_iso_generic regular node_deq edgePt smoothOffEdges exc_image flat isProper one_le_width edgePt_over comp toDR crossingPt DRResolvedModelCharts" end DRResolvedModelPackage
p2m_open_scoped "ModularCurve.DRResolvedModelPackage" in

theorem DRResolvedModelPackage.hdeg_chain_of_hdeg_alpha (n : node)
    {m : ℕ} (d : Fin m → ℕ) (pos neg : Fin m → ℕ) (aplus aminus : X0MqComponents width → ℕ)
    (vp vn : Fin (width n + 1) → ℕ)
    (hvp : ∀ k, vp k = aplus (DRResolvedModelPackage.chainPos width n k))
    (hvn : ∀ k, vn k = aminus (DRResolvedModelPackage.chainPos width n k))
    (halpha : ∀ i : Fin (width n - 1),
      (∑ j, if d j = (i : ℕ) + 1 then ((pos j : ℤ) - neg j) else 0) +
        intersectionAlpha (x0MqResolvedTable width) (fun F => (aplus F : ℤ) - aminus F) (Sum.inr ⟨n, i⟩) = 0) :
    ∀ k : ℕ, ∀ hk0 : 0 < k, ∀ hke : k < width n,
      (∑ j, if d j = k then ((pos j : ℤ) - neg j) else 0) +
        (((vp ⟨k - 1, by omega⟩ : ℤ) - vn ⟨k - 1, by omega⟩) - 2 * ((vp ⟨k, by omega⟩ : ℤ) - vn ⟨k, by omega⟩) +
          ((vp ⟨k + 1, by omega⟩ : ℤ) - vn ⟨k + 1, by omega⟩)) = 0 := by
  intro k hk0 hke
  have h := halpha ⟨k - 1, by omega⟩
  rw [intersectionAlpha_x0MqResolvedTable_inr] at h
  have hk1 : k - 1 + 1 = k := by omega
  have hk2 : k - 1 + 2 = k + 1 := by omega
  have hmid : DRResolvedModelPackage.chainPos width n k = Sum.inr ⟨n, ⟨k - 1, by omega⟩⟩ :=
    chainPos_of_pos_of_lt width n k (by omega) hke
  simp only [hk1, hk2] at h
  simp only [hvp, hvn, hmid]
  rw [← hmid]
  rw [← hmid] at h
  linarith

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"

p2m_open "CategoryTheory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.AlgebraicGeometry TopologicalSpace MvPolynomial P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.MvPolynomial MvPolynomial.CrossingQuotient P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.MvPolynomial.CrossingQuotient ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve MazurRapoportAppendix"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRResolvedModelPackage.chainPos DRModel.baseChangeMap DRResolvedModelPackage DRModel DRModel.toBase DRModelPackage X0MqComponents x0MqAdj x0MqAdj_symm x0MqResolvedTable DRResolvedModelPackage.DRResolvedModelCharts"
namespace DRResolvedModelPackage
p2m_export "ModularCurve.DRResolvedModelPackage" "chainPos toBase toDR_iso_smoothLocus node toDR_over isIntegral node_fintype comp_isInvertible width mk.injEq mk Y nodeEquiv toDR_iso_generic regular node_deq edgePt smoothOffEdges exc_image flat isProper one_le_width edgePt_over comp toDR crossingPt DRResolvedModelCharts"
p2m_open "ModularCurve.DRResolvedModelPackage ModularCurve"

variable {p : ℕ} [Fact p.Prime] {𝔛 : DRModelPackage p} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
  {𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ} {ϖ : O} {Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ϖ e).IdealSheafData}

namespace ChartWitness

private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.descLoc_call (𝒞 : 𝔛reg.ChartWitness ϖ Fc) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ})
    [IsSeparated (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (n : 𝔛reg.node)
    [IsIntegral (pullback (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)))]
    (hgen : ∃ y : ↥(pullback (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n))),
      (pullback.fst (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)) ≫ (𝒞.U n).ι ≫
          pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base y ≠
        IsLocalRing.closedPoint O)
    (hF : ∀ (e : ℕ) (i : Fin e) (k : Fin (e + 1)), (Fc e k).comap (Resolution.ι ϖ e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O ϖ))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {CrossingQuotient.V ϖ} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {CrossingQuotient.U ϖ} else ⊤)))
    {m₁ : ℕ} (σ' : Fin m₁ → (Spec (CommRingCat.of O) ⟶ pullback (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n))))
    (hσ' : ∀ j, σ' j ≫ pullback.fst (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)) ≫ (𝒞.U n).ι ≫
        pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) = 𝟙 _)
    (pos' neg' : Fin m₁ → ℕ) (d : Fin m₁ → ℕ) (hd : ∀ j, 0 < d j ∧ d j < 𝔛reg.width n)
    (hσd : ∀ j, (σ' j).base (IsLocalRing.closedPoint O) ∈
        ((Fc (𝔛reg.width n) ⟨d j, (hd j).2.trans (𝔛reg.width n).lt_succ_self⟩).comap
          (pullback.snd (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)))).support ∧
      ∀ k : Fin (𝔛reg.width n + 1), (k : ℕ) ≠ d j →
        (σ' j).base (IsLocalRing.closedPoint O) ∉
          ((Fc (𝔛reg.width n) k).comap (pullback.snd (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)))).support)
    {m₂ : ℕ} (J : Fin m₂ → (pullback (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n))).IdealSheafData)
    (hJ : ∀ i, (J i).IsInvertible)
    (hJs : ∀ i, ((J i).support : Set _) ∩
      (pullback.fst (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)) ≫ (𝒞.U n).ι ≫
        pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base ⁻¹' {IsLocalRing.closedPoint O} = ∅)
    (jp jn : Fin m₂ → ℕ) (aplus aminus : X0MqComponents 𝔛reg.width → ℕ)
    (halpha : ∀ i : Fin (𝔛reg.width n - 1),
      (∑ j, if d j = (i : ℕ) + 1 then ((pos' j : ℤ) - neg' j) else 0) +
        intersectionAlpha (x0MqResolvedTable 𝔛reg.width) (fun F => (aplus F : ℤ) - aminus F) (Sum.inr ⟨n, i⟩) = 0) :
    ∃ V : (DRModelPackage.XO p O).Opens, 𝔛reg.crossingPt n ∈ V ∧ V ≤ 𝒞.U n ∧
      Nonempty ((Scheme.Modules.pullback
          (pullback.fst (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)) ⁻¹ᵁ ((𝒞.U n).ι ⁻¹ᵁ V)).ι).obj
            ((List.finRange m₁).foldr
                (fun j M => ((((σ' j).ker) ^ pos' j).invModule ⊗ (((σ' j).ker) ^ neg' j).module) ⊗ M)
              ((List.finRange m₂).foldr (fun i M => (((J i) ^ jp i).invModule ⊗ ((J i) ^ jn i).module) ⊗ M)
                ((∏ k, (Fc (𝔛reg.width n) k).comap (pullback.snd (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n))) ^
                      aplus (DRResolvedModelPackage.chainPos 𝔛reg.width n k)).invModule ⊗
                  (∏ k, (Fc (𝔛reg.width n) k).comap (pullback.snd (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n))) ^
                      aminus (DRResolvedModelPackage.chainPos 𝔛reg.width n k)).module))) ≅
        𝟙_ _) := by
  classical
  letI := 𝔛reg.node_fintype
  letI := 𝔛reg.node_deq

  obtain ⟨hFc_inv, hFc_t, hFc_u, hFc_supp, hFc_vertex, hFc_node, hFc_sect⟩ :=
    MvPolynomial.CrossingQuotient.Resolution.specialFibrePackage_of_chartTable ϖ hϖ (𝔛reg.width n)
      (Fc (𝔛reg.width n)) (hF (𝔛reg.width n))

  have hdeg := DRResolvedModelPackage.hdeg_chain_of_hdeg_alpha 𝔛reg.width n d pos' neg' aplus aminus
    (fun k => aplus (DRResolvedModelPackage.chainPos 𝔛reg.width n k))
    (fun k => aminus (DRResolvedModelPackage.chainPos 𝔛reg.width n k)) (fun _ => rfl) (fun _ => rfl) halpha

  haveI : LocallyOfFiniteType (𝒞.f n) := inferInstance
  haveI : FormallyUnramified (𝒞.f n) := inferInstance
  exact MvPolynomial.CrossingQuotient.Resolution.exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero
    ϖ hϖ (𝔛reg.width n) (𝔛reg.one_le_width n)
    (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) (𝔛reg.crossingPt n) (𝒞.U n)
    (𝒞.mem_U n) (𝒞.f n) (𝒞.f_over n) (𝒞.f_mem_Vc_iff n) (𝒞.hinj n) hgen (Fc (𝔛reg.width n))
    hFc_inv hFc_t hFc_u hFc_supp hFc_vertex hFc_node hFc_sect σ' hσ' pos' neg' d hd hσd
    (fun k => aplus (DRResolvedModelPackage.chainPos 𝔛reg.width n k))
    (fun k => aminus (DRResolvedModelPackage.chainPos 𝔛reg.width n k)) J hJ hJs jp jn hdeg

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "descLoc_call"
end ChartWitness
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"

end ModularCurve.DRResolvedModelPackage
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"

end
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"

set_option autoImplicit false

p2m_open "CategoryTheory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.AlgebraicGeometry"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRResolvedModelPackage.chainPos DRModel.baseChangeMap DRResolvedModelPackage DRModel DRModel.toBase DRModelPackage X0MqComponents x0MqAdj x0MqAdj_symm x0MqResolvedTable DRResolvedModelPackage.DRResolvedModelCharts"
p2m_open "ModularCurve"

variable {p : ℕ} [Fact p.Prime]

p2m_open_scoped "ModularCurve.DRModelPackage" in

theorem DRModelPackage.isSeparated_snd_toBase (𝔛 : DRModelPackage p) (O : Type) [CommRing O] :
    IsSeparated (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) := by
  haveI := 𝔛.isProper
  infer_instance

p2m_open_scoped "ModularCurve.DRModelPackage" in

theorem DRModelPackage.isProper_snd_toBase (𝔛 : DRModelPackage p) (O : Type) [CommRing O] :
    IsProper (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) := by
  haveI := 𝔛.isProper
  infer_instance

namespace DRResolvedModelPackage
p2m_export "ModularCurve.DRResolvedModelPackage" "chainPos toBase toDR_iso_smoothLocus node toDR_over isIntegral node_fintype comp_isInvertible width mk.injEq mk Y nodeEquiv toDR_iso_generic regular node_deq edgePt smoothOffEdges exc_image flat isProper one_le_width edgePt_over comp toDR crossingPt DRResolvedModelCharts"
p2m_open "ModularCurve.DRResolvedModelPackage"

variable {𝔛 : DRModelPackage p} {O : Type} [CommRing O]
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
  (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ)

private theorem _root_.ModularCurve.DRResolvedModelPackage.edgePt_zero_mem_preimage_toDR (n : 𝔛reg.node)
    (U : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Opens)
    (hU : (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv n) ∈ U) :
    𝔛reg.edgePt n ⟨0, 𝔛reg.one_le_width n⟩ ∈ 𝔛reg.toDR ⁻¹ᵁ U := by
  change 𝔛reg.toDR.base (𝔛reg.edgePt n ⟨0, 𝔛reg.one_le_width n⟩) ∈ U
  rw [𝔛reg.edgePt_over]
  exact hU

p2m_export "ModularCurve.DRResolvedModelPackage" "edgePt_zero_mem_preimage_toDR"

private theorem _root_.ModularCurve.DRResolvedModelPackage.isIntegral_of_iso_preimage_toDR {P : Scheme.{0}}
    (U : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Opens)
    (Φ : P ≅ ↑(𝔛reg.toDR ⁻¹ᵁ U)) (y : 𝔛reg.Y) (hy : y ∈ 𝔛reg.toDR ⁻¹ᵁ U) : IsIntegral P := by
  haveI : Nonempty P := ⟨Φ.inv.base ⟨y, hy⟩⟩
  exact isIntegral_of_isOpenImmersion (Φ.hom ≫ (𝔛reg.toDR ⁻¹ᵁ U).ι)

p2m_export "ModularCurve.DRResolvedModelPackage" "isIntegral_of_iso_preimage_toDR"

private theorem _root_.ModularCurve.DRResolvedModelPackage.exists_mem_preimage_toDR_and_toBase_ne_closedPoint [IsDomain O] [IsDiscreteValuationRing O]
    (U : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Opens)
    (y : 𝔛reg.Y) (hy : y ∈ 𝔛reg.toDR ⁻¹ᵁ U) :
    ∃ y' : 𝔛reg.Y, y' ∈ 𝔛reg.toDR ⁻¹ᵁ U ∧ 𝔛reg.toBase.base y' ≠ IsLocalRing.closedPoint O := by
  let ξ : Spec (CommRingCat.of O) := ⟨⊥, Ideal.isPrime_bot⟩
  have hspec : ξ ⤳ 𝔛reg.toBase.base y := (PrimeSpectrum.le_iff_specializes ξ _).mp bot_le
  obtain ⟨y', hy'y, hy'⟩ := Flat.generalizingMap 𝔛reg.toBase hspec
  refine ⟨y', hy'y.mem_open (𝔛reg.toDR ⁻¹ᵁ U).isOpen hy, ?_⟩
  intro h
  have h' : (ξ : Spec (CommRingCat.of O)) = IsLocalRing.closedPoint O := hy'.symm.trans h
  exact IsDiscreteValuationRing.not_a_field O (congrArg PrimeSpectrum.asIdeal h').symm

p2m_export "ModularCurve.DRResolvedModelPackage" "exists_mem_preimage_toDR_and_toBase_ne_closedPoint"

private theorem _root_.ModularCurve.DRResolvedModelPackage.exists_pullback_base_ne_closedPoint [IsDomain O] [IsDiscreteValuationRing O]
    (U : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Opens)
    {S C : Scheme.{0}} (f : (U : Scheme.{0}) ⟶ S) (ρ : C ⟶ S)
    (Φ : pullback f ρ ≅ ↑(𝔛reg.toDR ⁻¹ᵁ U)) (Φ_fst : Φ.hom ≫ (𝔛reg.toDR ∣_ U) = pullback.fst f ρ)
    (y : 𝔛reg.Y) (hy : y ∈ 𝔛reg.toDR ⁻¹ᵁ U) :
    ∃ z : ↥(pullback f ρ),
      (pullback.fst f ρ ≫ U.ι ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base z ≠
        IsLocalRing.closedPoint O := by
  obtain ⟨y', hy'U, hne⟩ := 𝔛reg.exists_mem_preimage_toDR_and_toBase_ne_closedPoint U y hy
  refine ⟨Φ.inv.base ⟨y', hy'U⟩, ?_⟩
  have hcomp : pullback.fst f ρ ≫ U.ι ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
      Φ.hom ≫ (𝔛reg.toDR ⁻¹ᵁ U).ι ≫ 𝔛reg.toBase := by
    rw [← Φ_fst, Category.assoc, ← Category.assoc (𝔛reg.toDR ∣_ U), morphismRestrict_ι, Category.assoc,
      𝔛reg.toDR_over]
  rw [hcomp]
  change (Φ.inv ≫ Φ.hom ≫ (𝔛reg.toDR ⁻¹ᵁ U).ι ≫ 𝔛reg.toBase).base ⟨y', hy'U⟩ ≠ _
  rw [Iso.inv_hom_id_assoc]
  exact hne

p2m_export "ModularCurve.DRResolvedModelPackage" "exists_pullback_base_ne_closedPoint"

private theorem _root_.ModularCurve.DRResolvedModelPackage.isIntegral_pullback_of_iso_preimage_toDR
    (U : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Opens)
    {S C : Scheme.{0}} (f : (U : Scheme.{0}) ⟶ S) (ρ : C ⟶ S)
    (Φ : pullback f ρ ≅ ↑(𝔛reg.toDR ⁻¹ᵁ U)) (y : 𝔛reg.Y) (hy : y ∈ 𝔛reg.toDR ⁻¹ᵁ U) :
    IsIntegral (pullback f ρ) :=
  𝔛reg.isIntegral_of_iso_preimage_toDR U Φ y hy

p2m_export "ModularCurve.DRResolvedModelPackage" "isIntegral_pullback_of_iso_preimage_toDR"
end DRResolvedModelPackage
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"

end
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"

set_option autoImplicit false

p2m_open "CategoryTheory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.AlgebraicGeometry"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRResolvedModelPackage.chainPos DRModel.baseChangeMap DRResolvedModelPackage DRModel DRModel.toBase DRModelPackage X0MqComponents x0MqAdj x0MqAdj_symm x0MqResolvedTable DRResolvedModelPackage.DRResolvedModelCharts"
p2m_open "ModularCurve"

section Combinatorics

variable {node : Type} (width : node → ℕ)

theorem chainPos_zero' (n : node) : DRResolvedModelPackage.chainPos width n 0 = Sum.inl 0 := by
  simp [DRResolvedModelPackage.chainPos]

theorem chainPos_of_pos_of_lt' (n : node) (d : ℕ) (h0 : d ≠ 0) (hd : d < width n) :
    DRResolvedModelPackage.chainPos width n d = Sum.inr ⟨n, ⟨d - 1, by omega⟩⟩ := by
  simp [DRResolvedModelPackage.chainPos, h0, hd]

theorem chainPos_of_le' (n : node) (d : ℕ) (h0 : d ≠ 0) (hd : width n ≤ d) :
    DRResolvedModelPackage.chainPos width n d = Sum.inl 1 := by
  simp [DRResolvedModelPackage.chainPos, h0, not_lt.mpr hd]

theorem chainPos_decode (n : node) (d : ℕ) (hd : d ≤ width n) :
    Sum.elim (fun j : Fin 2 => (j : ℕ) * width n) (fun q : (Σ x : node, Fin (width x - 1)) => (q.2 : ℕ) + 1)
      (DRResolvedModelPackage.chainPos width n d) = d := by
  by_cases h0 : d = 0
  · subst h0; simp [chainPos_zero']
  · by_cases hlt : d < width n
    · rw [chainPos_of_pos_of_lt' width n d h0 hlt]; simp only [Sum.elim_inr]; omega
    · rw [chainPos_of_le' width n d h0 (not_lt.mp hlt)]; simp only [Sum.elim_inl, Fin.val_one, one_mul]; omega

theorem chainPos_injective (n : node) :
    Function.Injective (fun d : Fin (width n + 1) => DRResolvedModelPackage.chainPos width n d) := by
  intro d₁ d₂ h
  apply Fin.ext
  have h1 := chainPos_decode width n d₁ (by have := d₁.isLt; omega)
  have h2 := chainPos_decode width n d₂ (by have := d₂.isLt; omega)
  simp only at h
  rw [← h1, ← h2, h]

theorem exists_eq_inr_of_forall_ne_chainPos (n : node) (hn : 1 ≤ width n) (F : X0MqComponents width)
    (hF : ∀ d : Fin (width n + 1), F ≠ DRResolvedModelPackage.chainPos width n d) :
    ∃ (n' : node) (i : Fin (width n' - 1)), F = Sum.inr ⟨n', i⟩ ∧ n' ≠ n := by
  rcases F with j | ⟨n', i⟩
  · exfalso
    have hw : width n ≠ 0 := by omega
    fin_cases j
    · exact hF ⟨0, by omega⟩ (by simp [DRResolvedModelPackage.chainPos])
    · exact hF ⟨width n, by omega⟩ (by simp [DRResolvedModelPackage.chainPos, hw])
  · refine ⟨n', i, rfl, fun h => ?_⟩
    subst h
    have hi := i.isLt
    exact hF ⟨(i : ℕ) + 1, by omega⟩
      (by rw [Fin.val_mk, chainPos_of_pos_of_lt' width n' ((i : ℕ) + 1) (by omega) (by omega)]; rfl)

end Combinatorics
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"

namespace DRResolvedModelPackage
p2m_export "ModularCurve.DRResolvedModelPackage" "chainPos toBase toDR_iso_smoothLocus node toDR_over isIntegral node_fintype comp_isInvertible width mk.injEq mk Y nodeEquiv toDR_iso_generic regular node_deq edgePt smoothOffEdges exc_image flat isProper one_le_width edgePt_over comp toDR crossingPt DRResolvedModelCharts"
p2m_open "ModularCurve.DRResolvedModelPackage"

variable {p : ℕ} [Fact p.Prime] {𝔛 : DRModelPackage p} {O : Type} [CommRing O]
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
  (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ)

private theorem _root_.ModularCurve.DRResolvedModelPackage.forall_notMem_support_comp_of_forall_ne_chainPos (n : 𝔛reg.node)
    (U : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Opens)
    (hU : ∀ m : 𝔛reg.node, m ≠ n →
      (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv m) ∉ U)
    {P : Scheme.{0}} (ψ : P ⟶ 𝔛reg.Y) (hψ : ∀ z : P, 𝔛reg.toDR.base (ψ.base z) ∈ U)
    (F : X0MqComponents 𝔛reg.width) (hF : ∀ d : Fin (𝔛reg.width n + 1), F ≠ DRResolvedModelPackage.chainPos 𝔛reg.width n d) :
    ∀ z : P, ψ.base z ∉ ((𝔛reg.comp F).support : Set 𝔛reg.Y) := by
  obtain ⟨n', i, rfl, hn'⟩ := exists_eq_inr_of_forall_ne_chainPos 𝔛reg.width n (𝔛reg.one_le_width n) F hF
  intro z hz
  apply hU n' hn'
  rw [← 𝔛reg.exc_image n' i (ψ.base z) hz]
  exact hψ z

p2m_export "ModularCurve.DRResolvedModelPackage" "forall_notMem_support_comp_of_forall_ne_chainPos"

private theorem _root_.ModularCurve.DRResolvedModelPackage.comap_comp_eq_top_of_forall_ne_chainPos (n : 𝔛reg.node)
    (U : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Opens)
    (hU : ∀ m : 𝔛reg.node, m ≠ n →
      (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv m) ∉ U)
    {P : Scheme.{0}} (ψ : P ⟶ 𝔛reg.Y) (hψ : ∀ z : P, 𝔛reg.toDR.base (ψ.base z) ∈ U)
    (F : X0MqComponents 𝔛reg.width) (hF : ∀ d : Fin (𝔛reg.width n + 1), F ≠ DRResolvedModelPackage.chainPos 𝔛reg.width n d) :
    (𝔛reg.comp F).comap ψ = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_comap]
  ext z
  simp only [TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage, TopologicalSpace.Closeds.coe_bot,
    Set.mem_empty_iff_false, iff_false]
  exact 𝔛reg.forall_notMem_support_comp_of_forall_ne_chainPos n U hU ψ hψ F hF z

p2m_export "ModularCurve.DRResolvedModelPackage" "comap_comp_eq_top_of_forall_ne_chainPos"

private theorem _root_.ModularCurve.DRResolvedModelPackage.toDR_base_mem_of_comp_ι {P : Scheme.{0}}
    (U : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Opens)
    (φ : P ⟶ ↑(𝔛reg.toDR ⁻¹ᵁ U)) (z : P) : 𝔛reg.toDR.base ((φ ≫ (𝔛reg.toDR ⁻¹ᵁ U).ι).base z) ∈ U := by
  rw [Scheme.Hom.comp_base, TopCat.comp_app]
  exact (φ.base z).2

p2m_export "ModularCurve.DRResolvedModelPackage" "toDR_base_mem_of_comp_ι"
end DRResolvedModelPackage
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"

end
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage"

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRResolvedModelPackage.chainPos DRModel.baseChangeMap DRResolvedModelPackage DRModel DRModel.toBase DRModelPackage X0MqComponents x0MqAdj x0MqAdj_symm x0MqResolvedTable DRResolvedModelPackage.DRResolvedModelCharts"
p2m_open "ModularCurve"

variable {node : Type} [DecidableEq node] (width : node → ℕ) {m : ℕ}
  (v : Fin m → X0MqComponents width) (n : node)

def IsNear (j : Fin m) : Prop := ∃ i : Fin (width n - 1), v j = Sum.inr ⟨n, i⟩

scoped instance IsNear.decidablePred : DecidablePred (IsNear width v n) := Classical.decPred _

p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.IsNear"

def nearIdx (j : {j // IsNear width v n j}) : Fin (width n - 1) := j.2.choose

theorem v_eq_inr_nearIdx (j : {j // IsNear width v n j}) : v j.1 = Sum.inr ⟨n, nearIdx width v n j⟩ :=
  j.2.choose_spec

def nearCard : ℕ := Fintype.card {j // IsNear width v n j}

def farCard : ℕ := Fintype.card {j // ¬ IsNear width v n j}

def nearFarEquiv : Fin (nearCard width v n) ⊕ Fin (farCard width v n) ≃ Fin m :=
  (Equiv.sumCongr (Fintype.equivFin {j // IsNear width v n j}).symm
      (Fintype.equivFin {j // ¬ IsNear width v n j}).symm).trans
    (Equiv.sumCompl (IsNear width v n))

theorem isNear_nearFarEquiv_inl (i : Fin (nearCard width v n)) :
    IsNear width v n (nearFarEquiv width v n (Sum.inl i)) :=
  ((Fintype.equivFin {j // IsNear width v n j}).symm i).2

theorem not_isNear_nearFarEquiv_inr (i : Fin (farCard width v n)) :
    ¬ IsNear width v n (nearFarEquiv width v n (Sum.inr i)) :=
  ((Fintype.equivFin {j // ¬ IsNear width v n j}).symm i).2

theorem nearCard_add_farCard : nearCard width v n + farCard width v n = m := by
  simpa using Fintype.card_congr (nearFarEquiv width v n)

def nearChainPos (i : Fin (nearCard width v n)) : ℕ :=
  (nearIdx width v n ⟨_, isNear_nearFarEquiv_inl width v n i⟩ : ℕ) + 1

theorem nearChainPos_pos_and_lt (i : Fin (nearCard width v n)) :
    0 < nearChainPos width v n i ∧ nearChainPos width v n i < width n := by
  have := (nearIdx width v n ⟨_, isNear_nearFarEquiv_inl width v n i⟩).isLt
  simp only [nearChainPos]
  omega

theorem v_nearFarEquiv_inl (i : Fin (nearCard width v n)) :
    v (nearFarEquiv width v n (Sum.inl i)) =
      Sum.inr ⟨n, ⟨nearChainPos width v n i - 1, by have := nearChainPos_pos_and_lt width v n i; omega⟩⟩ := by
  rw [v_eq_inr_nearIdx width v n ⟨_, isNear_nearFarEquiv_inl width v n i⟩]
  simp only [nearChainPos, Nat.add_sub_cancel, Fin.eta]

theorem v_nearFarEquiv_inr_ne (i : Fin (farCard width v n)) (k : Fin (width n - 1)) :
    v (nearFarEquiv width v n (Sum.inr i)) ≠ Sum.inr ⟨n, k⟩ :=
  fun h => not_isNear_nearFarEquiv_inr width v n i ⟨k, h⟩

theorem sum_single_inr_eq_sum_near (pos neg : Fin m → ℕ) (i : Fin (width n - 1)) :
    (∑ j : Fin m, Finsupp.single (v j) ((pos j : ℤ) - (neg j : ℤ))) (Sum.inr ⟨n, i⟩) =
      ∑ j : Fin (nearCard width v n), if nearChainPos width v n j = (i : ℕ) + 1 then
        ((pos (nearFarEquiv width v n (Sum.inl j)) : ℤ) - neg (nearFarEquiv width v n (Sum.inl j))) else 0 := by
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  rw [← Equiv.sum_comp (nearFarEquiv width v n), Fintype.sum_sum_type]
  have hfar : ∑ k : Fin (farCard width v n),
      (if v (nearFarEquiv width v n (Sum.inr k)) = Sum.inr ⟨n, i⟩ then
        ((pos (nearFarEquiv width v n (Sum.inr k)) : ℤ) - neg (nearFarEquiv width v n (Sum.inr k))) else 0) = 0 :=
    Finset.sum_eq_zero fun k _ => if_neg (v_nearFarEquiv_inr_ne width v n k i)
  rw [hfar, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hv := v_eq_inr_nearIdx width v n ⟨_, isNear_nearFarEquiv_inl width v n k⟩
  simp only at hv
  have hiff : v (nearFarEquiv width v n (Sum.inl k)) = Sum.inr ⟨n, i⟩ ↔ nearChainPos width v n k = (i : ℕ) + 1 := by
    rw [hv]
    simp only [nearChainPos, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, true_and, Fin.ext_iff]
    omega
  by_cases hk : nearChainPos width v n k = (i : ℕ) + 1
  · rw [if_pos (hiff.mpr hk), if_pos hk]
  · rw [if_neg (fun h => hk (hiff.mp h)), if_neg hk]

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.IsNear"

end
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.IsNear"

set_option autoImplicit false

p2m_open "CategoryTheory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.AlgebraicGeometry TopologicalSpace MvPolynomial P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.MvPolynomial MvPolynomial.CrossingQuotient P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.MvPolynomial.CrossingQuotient ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRResolvedModelPackage.chainPos DRModel.baseChangeMap DRResolvedModelPackage DRModel DRModel.toBase DRModelPackage X0MqComponents x0MqAdj x0MqAdj_symm x0MqResolvedTable DRResolvedModelPackage.DRResolvedModelCharts"
namespace DRResolvedModelPackage
p2m_export "ModularCurve.DRResolvedModelPackage" "chainPos toBase toDR_iso_smoothLocus node toDR_over isIntegral node_fintype comp_isInvertible width mk.injEq mk Y nodeEquiv toDR_iso_generic regular node_deq edgePt smoothOffEdges exc_image flat isProper one_le_width edgePt_over comp toDR crossingPt DRResolvedModelCharts"
p2m_open "ModularCurve.DRResolvedModelPackage ModularCurve"

variable {p : ℕ} [Fact p.Prime] {𝔛 : DRModelPackage p} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
  {𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ} {ϖ : O} {Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ϖ e).IdealSheafData}

namespace ChartWitness

omit [IsDomain O] [IsDiscreteValuationRing O] in

private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.combine (𝒞 : 𝔛reg.ChartWitness ϖ Fc) (n : 𝔛reg.node) (L : 𝔛reg.Y.Modules)
    (Mloc : (pullback (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n))).Modules)
    (eT : Nonempty ((Scheme.Modules.pullback (𝒞.ψ n)).obj L ≅ Mloc))
    (V : (DRModelPackage.XO p O).Opens) (hV : V ≤ 𝒞.U n)
    (τ : Nonempty ((Scheme.Modules.pullback
      (pullback.fst (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)) ⁻¹ᵁ ((𝒞.U n).ι ⁻¹ᵁ V)).ι).obj Mloc ≅ 𝟙_ _)) :
    Nonempty ((Scheme.Modules.pullback (𝔛reg.toDR ⁻¹ᵁ V).ι).obj L ≅
      SheafOfModules.unit (𝔛reg.toDR ⁻¹ᵁ V).toScheme.ringCatSheaf) := by
  obtain ⟨e⟩ := eT
  obtain ⟨t⟩ := τ

  have hW : 𝔛reg.toDR ⁻¹ᵁ V ≤ (𝒞.ψ n).opensRange := by
    rw [𝒞.opensRange_ψ n]
    exact fun y hy => hV hy
  refine AlgebraicGeometry.Scheme.Modules.nonempty_pullback_iso_unit_of_isOpenImmersion (𝒞.ψ n) L (𝔛reg.toDR ⁻¹ᵁ V) hW ?_

  have heq : (𝒞.ψ n) ⁻¹ᵁ (𝔛reg.toDR ⁻¹ᵁ V) =
      pullback.fst (𝒞.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)) ⁻¹ᵁ ((𝒞.U n).ι ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, 𝒞.ψ_toDR n, Scheme.Hom.comp_preimage]
  rw [heq]
  exact ⟨(Scheme.Modules.pullback _).mapIso e ≪≫ t⟩

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "combine"
end ChartWitness
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.IsNear"

end ModularCurve.DRResolvedModelPackage
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.IsNear"
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.IsNear"

end
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.IsNear"

set_option autoImplicit false

p2m_open "CategoryTheory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.AlgebraicGeometry TopologicalSpace MvPolynomial P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.MvPolynomial MvPolynomial.CrossingQuotient P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.MvPolynomial.CrossingQuotient ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve"

noncomputable section

namespace MvPolynomial
p2m_export "MvPolynomial" "comap_comp X map R funext ext support comap C mem_zeroLocus_iff zeroLocus_span supported CrossingQuotient.Resolution CrossingQuotient.U CrossingQuotient.V CrossingQuotient CrossingQuotient.Resolution.specialFibrePackage_of_chartTable CrossingQuotient.Resolution.exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero"
namespace CrossingQuotient
p2m_export "MvPolynomial.CrossingQuotient" "twist crossingScheme chartScheme Resolution Resolution.ι Resolution.toCrossing U V lift resolutionChart resolutionChart_U resolutionChart_V mk Resolution.specialFibrePackage_of_chartTable Resolution.exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero"
namespace Resolution
p2m_export "MvPolynomial.CrossingQuotient.Resolution" "ι exists_ι_apply_eq toCrossing ι_toCrossing specialFibrePackage_of_chartTable exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero"
p2m_open "MvPolynomial.CrossingQuotient.Resolution MvPolynomial.CrossingQuotient MvPolynomial"

variable {W : Type} [CommRing W] (t : W) (e : ℕ)

theorem ι_apply_mem_support_iff_of_comap_ι_eq (F : (Resolution t e).IdealSheafData) (i : Fin e)
    (J : Ideal (CrossingQuotient W t))
    (h : F.comap (ι t e i) = Scheme.IdealSheafData.ofIdealTop (J.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W t))).inv.hom))
    (z : chartScheme t) : ι t e i z ∈ F.support ↔ (J : Set (CrossingQuotient W t)) ⊆ z.asIdeal := by
  have h1 : z ∈ (F.comap (ι t e i)).support ↔ ι t e i z ∈ F.support := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  rw [← h1, h, ← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_ofIdealTop, Ideal.map, Scheme.zeroLocus_span,
    Scheme.mem_zeroLocus_iff]
  constructor
  · intro H j hj
    have := H _ ⟨j, hj, rfl⟩
    rw [basicOpen_eq_of_affine] at this
    by_contra hjz
    exact this hjz
  · rintro H _ ⟨j, hj, rfl⟩
    rw [basicOpen_eq_of_affine]
    exact fun hz => hz (H hj)

variable {t e} in
theorem toCrossing_ι_apply_asIdeal (i : Fin e) (z : chartScheme t) :
    (toCrossing t e (ι t e i z)).asIdeal = Ideal.comap (resolutionChart t e i).toRingHom z.asIdeal := by
  rw [← Scheme.Hom.comp_apply, ι_toCrossing]; rfl

theorem mem_support_one_of_mem_support_zero (F : Fin (e + 1) → (Resolution t e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (ι t e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W t))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {V t} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U t} else ⊤)))
    (he : 0 < e) (y : ↥(Resolution t e)) (h0 : y ∈ (F 0).support)
    (hu : CrossingQuotient.U (t ^ e) ∈ (toCrossing t e y).asIdeal) : y ∈ (F ⟨1, by omega⟩).support := by
  obtain ⟨i, z, rfl⟩ := exists_ι_apply_eq t e y
  have hi : (i : ℕ) = 0 := by
    by_contra hi
    have htab := hF i 0
    rw [if_neg (fun h : ((0 : Fin (e + 1)) : ℕ) = (i : ℕ) => hi (by simpa using h.symm)),
      if_neg (fun h : ((0 : Fin (e + 1)) : ℕ) = (i : ℕ) + 1 => by simp at h)] at htab
    have := (ι_apply_mem_support_iff_of_comap_ι_eq t e (F 0) i ⊤ htab z).mp h0
    exact z.isPrime.ne_top (top_le_iff.mp (fun x _ => this trivial))
  have hx : U t ∈ z.asIdeal := by
    rw [toCrossing_ι_apply_asIdeal, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, resolutionChart_U, hi,
      pow_zero, map_one, one_mul] at hu
    exact hu
  have htab := hF i ⟨1, by omega⟩
  rw [if_neg (fun h : ((⟨1, by omega⟩ : Fin (e + 1)) : ℕ) = (i : ℕ) => by simp [hi] at h),
    if_pos (show ((⟨1, by omega⟩ : Fin (e + 1)) : ℕ) = (i : ℕ) + 1 by simp [hi])] at htab
  rw [ι_apply_mem_support_iff_of_comap_ι_eq t e _ i _ htab]
  simpa [Ideal.span_le] using hx

theorem mem_support_pred_of_mem_support_last (F : Fin (e + 1) → (Resolution t e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (ι t e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W t))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {V t} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U t} else ⊤)))
    (he : 0 < e) (y : ↥(Resolution t e)) (h0 : y ∈ (F ⟨e, by omega⟩).support)
    (hv : CrossingQuotient.V (t ^ e) ∈ (toCrossing t e y).asIdeal) : y ∈ (F ⟨e - 1, by omega⟩).support := by
  obtain ⟨i, z, rfl⟩ := exists_ι_apply_eq t e y
  have hi : (i : ℕ) = e - 1 := by
    by_contra hi
    have htab := hF i ⟨e, by omega⟩
    rw [if_neg (fun h : ((⟨e, by omega⟩ : Fin (e + 1)) : ℕ) = (i : ℕ) => by simp at h; have := i.2; omega),
      if_neg (fun h : ((⟨e, by omega⟩ : Fin (e + 1)) : ℕ) = (i : ℕ) + 1 => hi (by simp at h; omega))] at htab
    have := (ι_apply_mem_support_iff_of_comap_ι_eq t e _ i ⊤ htab z).mp h0
    exact z.isPrime.ne_top (top_le_iff.mp (fun x _ => this trivial))
  have hy : V t ∈ z.asIdeal := by
    rw [toCrossing_ι_apply_asIdeal, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, resolutionChart_V, hi,
      show e - 1 - (e - 1) = 0 by omega, pow_zero, map_one, one_mul] at hv
    exact hv
  have htab := hF i ⟨e - 1, by omega⟩
  rw [if_pos (show ((⟨e - 1, by omega⟩ : Fin (e + 1)) : ℕ) = (i : ℕ) by simp [hi])] at htab
  rw [ι_apply_mem_support_iff_of_comap_ι_eq t e _ i _ htab]
  simpa [Ideal.span_le] using hy

theorem U_mem_and_V_mem_of_not_mem_sup {s : W} (x : crossingScheme s)
    (hx : x ∉ ((PrimeSpectrum.basicOpen (CrossingQuotient.U s) : (crossingScheme s).Opens) ⊔
      (PrimeSpectrum.basicOpen (CrossingQuotient.V s) : (crossingScheme s).Opens))) :
    CrossingQuotient.U s ∈ x.asIdeal ∧ CrossingQuotient.V s ∈ x.asIdeal := by
  have h1 : x ∉ (PrimeSpectrum.basicOpen (CrossingQuotient.U s) : (crossingScheme s).Opens) :=
    fun h => hx (Opens.mem_sup.mpr (Or.inl h))
  have h2 : x ∉ (PrimeSpectrum.basicOpen (CrossingQuotient.V s) : (crossingScheme s).Opens) :=
    fun h => hx (Opens.mem_sup.mpr (Or.inr h))
  exact ⟨not_not.mp h1, not_not.mp h2⟩

end MvPolynomial.CrossingQuotient.Resolution
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.IsNear"
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.IsNear"
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.IsNear"

namespace ModularCurve
p2m_export "ModularCurve" "DRResolvedModelPackage.chainPos DRModel.baseChangeMap DRResolvedModelPackage DRModel DRModel.toBase DRModelPackage X0MqComponents x0MqAdj x0MqAdj_symm x0MqResolvedTable DRResolvedModelPackage.DRResolvedModelCharts"
namespace DRResolvedModelPackage
p2m_export "ModularCurve.DRResolvedModelPackage" "chainPos toBase toDR_iso_smoothLocus node toDR_over isIntegral node_fintype comp_isInvertible width mk.injEq mk Y nodeEquiv toDR_iso_generic regular node_deq edgePt smoothOffEdges exc_image flat isProper one_le_width edgePt_over comp toDR crossingPt DRResolvedModelCharts"
p2m_open "ModularCurve.DRResolvedModelPackage ModularCurve"

variable {p : ℕ} [Fact p.Prime] {𝔛 : DRModelPackage p} {O : Type} [CommRing O]
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
  {𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ} {ϖ : O} {Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ϖ e).IdealSheafData}

section sect
variable [IsDomain O] [IsDiscreteValuationRing O]

theorem isClosedImmersion_and_isInvertible_ker_section
    (σ : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase)
    (hσ : σ.1.base (IsLocalRing.closedPoint O) ∈ 𝔛reg.smoothOffEdges) :
    IsClosedImmersion σ.1 ∧ (σ.1.ker).IsInvertible := by
  have h1 : IsClosedImmersion σ.1 := by
    have : IsClosedImmersion (σ.1 ≫ 𝔛reg.toBase) := by rw [σ.2]; infer_instance
    exact .of_comp σ.1 𝔛reg.toBase
  exact ⟨h1, Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens 𝔛reg.toBase 𝔛reg.smoothOffEdges σ.1 σ.2 hσ⟩

theorem isClosed_singleton_toDR_closedPoint
    (σ : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase)
    (hσ : (σ.1).base (IsLocalRing.closedPoint O) ∈ 𝔛reg.smoothOffEdges) :
    IsClosed ({𝔛reg.toDR.base (σ.1.base (IsLocalRing.closedPoint O))} : Set ↥(DRModelPackage.XO p O)) := by
  have h1 : IsClosedImmersion σ.1 := by
    have : IsClosedImmersion (σ.1 ≫ 𝔛reg.toBase) := by rw [σ.2]; infer_instance
    exact .of_comp σ.1 𝔛reg.toBase
  have hc : IsClosed ({IsLocalRing.closedPoint O} : Set (PrimeSpectrum O)) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr (IsLocalRing.maximalIdeal.isMaximal O)
  have h2 : IsClosed ({σ.1.base (IsLocalRing.closedPoint O)} : Set 𝔛reg.Y) := by
    convert σ.1.isClosedEmbedding.isClosedMap _ hc using 1
    exact Set.image_singleton.symm
  convert 𝔛reg.toDR.isClosedMap _ h2 using 1
  exact Set.image_singleton.symm

theorem toDR_closedPoint_ne_crossingPt_of_forall_ne_inr (𝒞 : 𝔛reg.ChartWitness ϖ Fc)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ})
    (hF : ∀ (e : ℕ) (i : Fin e) (k : Fin (e + 1)), (Fc e k).comap (Resolution.ι ϖ e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O ϖ))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {CrossingQuotient.V ϖ}
          else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {CrossingQuotient.U ϖ} else ⊤)))
    (n : 𝔛reg.node) (σ : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase)
    (w : X0MqComponents 𝔛reg.width)
    (hv : (σ.1).base (IsLocalRing.closedPoint O) ∈ 𝔛reg.smoothOffEdges ∧
        (σ.1).base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp w).support ∧
        ∀ w', w' ≠ w → (σ.1).base (IsLocalRing.closedPoint O) ∉ (𝔛reg.comp w').support)
    (hfar : ∀ i : Fin (𝔛reg.width n - 1), w ≠ Sum.inr ⟨n, i⟩) :
    𝔛reg.toDR.base ((σ.1).base (IsLocalRing.closedPoint O)) ≠ 𝔛reg.crossingPt n := by
  set pt := (σ.1).base (IsLocalRing.closedPoint O) with hpt
  intro heq
  obtain ⟨hsm, hw, hw'⟩ := hv
  rcases w with b | ⟨n', i⟩
  ·
    set e := 𝔛reg.width n with he_def
    have he : 0 < e := 𝔛reg.one_le_width n
    have hmem : pt ∈ (𝒞.ψ n).opensRange := by
      rw [𝒞.opensRange_ψ n]
      change 𝔛reg.toDR.base pt ∈ 𝒞.U n
      rw [heq]; exact 𝒞.mem_U n
    obtain ⟨y, hy⟩ := hmem

    have keyψ : ∀ (I : 𝔛reg.Y.IdealSheafData), y ∈ (I.comap (𝒞.ψ n)).support ↔ (𝒞.ψ n).base y ∈ I.support :=
      fun I => by rw [Scheme.IdealSheafData.support_comap]; rfl
    have keysnd : ∀ (I : (Resolution ϖ e).IdealSheafData),
        y ∈ (I.comap (pullback.snd (𝒞.f n) (Resolution.toCrossing ϖ e))).support ↔
          (pullback.snd (𝒞.f n) (Resolution.toCrossing ϖ e)).base y ∈ I.support :=
      fun I => by rw [Scheme.IdealSheafData.support_comap]; rfl
    have hlab : ∀ d : Fin (e + 1), pt ∈ (𝔛reg.comp (DRResolvedModelPackage.chainPos 𝔛reg.width n d)).support ↔
        (pullback.snd (𝒞.f n) (Resolution.toCrossing ϖ e)).base y ∈ (Fc e d).support := fun d => by
      rw [← hy, ← keyψ, 𝒞.label_ψ n d, keysnd]

    have hfst : ((pullback.fst (𝒞.f n) (Resolution.toCrossing ϖ e)).base y).1 = 𝔛reg.crossingPt n := by
      rw [← heq, ← hy]
      change _ = ((𝒞.ψ n ≫ 𝔛reg.toDR).base y)
      rw [𝒞.ψ_toDR n]; rfl
    have hvert : CrossingQuotient.U (ϖ ^ e) ∈ ((Resolution.toCrossing ϖ e).base ((pullback.snd (𝒞.f n) (Resolution.toCrossing ϖ e)).base y)).asIdeal ∧
        CrossingQuotient.V (ϖ ^ e) ∈ ((Resolution.toCrossing ϖ e).base ((pullback.snd (𝒞.f n) (Resolution.toCrossing ϖ e)).base y)).asIdeal := by
      have h1 : (𝒞.f n).base ((pullback.fst (𝒞.f n) (Resolution.toCrossing ϖ e)).base y) ∉
          ((PrimeSpectrum.basicOpen (CrossingQuotient.U (ϖ ^ e)) : (crossingScheme (ϖ ^ e)).Opens) ⊔
            (PrimeSpectrum.basicOpen (CrossingQuotient.V (ϖ ^ e)) : (crossingScheme (ϖ ^ e)).Opens)) := by
        rw [𝒞.f_mem_Vc_iff n]; exact fun h => h hfst
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply] at h1
      exact Resolution.U_mem_and_V_mem_of_not_mem_sup _ h1
    fin_cases b
    ·
      have h0 : pt ∈ (𝔛reg.comp (DRResolvedModelPackage.chainPos 𝔛reg.width n (0 : Fin (e + 1)))).support := by
        simpa [DRResolvedModelPackage.chainPos] using hw
      have h1 := Resolution.mem_support_one_of_mem_support_zero ϖ e (Fc e) (hF e) he _ ((hlab 0).mp h0) hvert.1
      have h1' : pt ∈ (𝔛reg.comp (DRResolvedModelPackage.chainPos 𝔛reg.width n (⟨1, by omega⟩ : Fin (e + 1)))).support :=
        (hlab ⟨1, by omega⟩).mpr h1
      refine hw' _ ?_ h1'
      simp only [DRResolvedModelPackage.chainPos, one_ne_zero, dif_neg, not_false_eq_true]
      split_ifs <;> simp
    ·
      have h0 : pt ∈ (𝔛reg.comp (DRResolvedModelPackage.chainPos 𝔛reg.width n (⟨e, by omega⟩ : Fin (e + 1)))).support := by
        have : DRResolvedModelPackage.chainPos 𝔛reg.width n ((⟨e, by omega⟩ : Fin (e + 1)) : ℕ) = Sum.inl 1 := by
          simp only [DRResolvedModelPackage.chainPos]
          rw [dif_neg (show ¬ (e = 0) by omega), dif_neg (show ¬ (e < e) from lt_irrefl e)]
        rw [this]; exact hw
      have h1 := Resolution.mem_support_pred_of_mem_support_last ϖ e (Fc e) (hF e) he _ ((hlab ⟨e, by omega⟩).mp h0) hvert.2
      have h1' : pt ∈ (𝔛reg.comp (DRResolvedModelPackage.chainPos 𝔛reg.width n (⟨e - 1, by omega⟩ : Fin (e + 1)))).support :=
        (hlab ⟨e - 1, by omega⟩).mpr h1
      refine hw' _ ?_ h1'
      simp only [DRResolvedModelPackage.chainPos]
      split_ifs with h0' h1'' <;> simp
      omega
  ·
    by_cases hn : n' = n
    · subst hn; exact hfar i rfl
    · have h1 : 𝔛reg.toDR.base pt = 𝔛reg.crossingPt n' := 𝔛reg.exc_image n' i pt hw
      rw [heq] at h1
      exact 𝒞.not_mem_U n n' hn (h1 ▸ 𝒞.mem_U n)

end sect
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.IsNear"

end ModularCurve.DRResolvedModelPackage
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.IsNear"
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.IsNear"

end
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.IsNear"

set_option autoImplicit false

p2m_open "CategoryTheory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.AlgebraicGeometry TopologicalSpace MvPolynomial P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.MvPolynomial MvPolynomial.CrossingQuotient P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.MvPolynomial.CrossingQuotient ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve MazurRapoportAppendix NeronModelInfra"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRResolvedModelPackage.chainPos DRModel.baseChangeMap DRResolvedModelPackage DRModel DRModel.toBase DRModelPackage X0MqComponents x0MqAdj x0MqAdj_symm x0MqResolvedTable DRResolvedModelPackage.DRResolvedModelCharts"
namespace DRResolvedModelPackage
p2m_export "ModularCurve.DRResolvedModelPackage" "chainPos toBase toDR_iso_smoothLocus node toDR_over isIntegral node_fintype comp_isInvertible width mk.injEq mk Y nodeEquiv toDR_iso_generic regular node_deq edgePt smoothOffEdges exc_image flat isProper one_le_width edgePt_over comp toDR crossingPt DRResolvedModelCharts"
p2m_open "ModularCurve.DRResolvedModelPackage ModularCurve"

variable {p : ℕ} [Fact p.Prime] {𝔛 : DRModelPackage p} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
  {𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ} {ϖ : O} {Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ϖ e).IdealSheafData}

namespace ChartWitness

private theorem _root_.ModularCurve.DRResolvedModelPackage.ChartWitness.exists_open_pullback_iso_unit (𝒞 : 𝔛reg.ChartWitness ϖ Fc)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ})
    (hF : ∀ (e : ℕ) (i : Fin e) (k : Fin (e + 1)), (Fc e k).comap (Resolution.ι ϖ e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O ϖ))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {CrossingQuotient.V ϖ}
          else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {CrossingQuotient.U ϖ} else ⊤)))
    {m : ℕ} (σ : Fin m → NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase) (pos neg : Fin m → ℕ)
    (v : Fin m → X0MqComponents 𝔛reg.width)
    (hv : ∀ j, (σ j).1.base (IsLocalRing.closedPoint O) ∈ 𝔛reg.smoothOffEdges ∧
        (σ j).1.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp (v j)).support ∧
        ∀ w, w ≠ v j → (σ j).1.base (IsLocalRing.closedPoint O) ∉ (𝔛reg.comp w).support)
    (aplus aminus : X0MqComponents 𝔛reg.width → ℕ)
    (hdeg : ∀ (nd : 𝔛reg.node) (i : Fin (𝔛reg.width nd - 1)),
        (∑ j, Finsupp.single (v j) ((pos j : ℤ) - (neg j : ℤ))) (Sum.inr ⟨nd, i⟩) +
          MazurRapoportAppendix.intersectionAlpha (x0MqResolvedTable 𝔛reg.width)
            (fun F => ((aplus F : ℤ) - (aminus F : ℤ))) (Sum.inr ⟨nd, i⟩) = 0)
    (n : 𝔛reg.node) :
    ∃ V : (DRModelPackage.XO p O).Opens, 𝔛reg.crossingPt n ∈ V ∧ V ≤ 𝒞.U n ∧
      Nonempty ((Scheme.Modules.pullback (𝔛reg.toDR ⁻¹ᵁ V).ι).obj (𝔛reg.divisorialSheaf σ pos neg aplus aminus) ≅
        SheafOfModules.unit (𝔛reg.toDR ⁻¹ᵁ V).toScheme.ringCatSheaf) := by
  classical
  letI := 𝔛reg.node_fintype
  letI := 𝔛reg.node_deq
  have hsect : ∀ j, IsClosedImmersion (σ j).1 ∧ ((σ j).1.ker).IsInvertible := fun j =>
    isClosedImmersion_and_isInvertible_ker_section (σ j) (hv j).1
  haveI : ∀ j, IsClosedImmersion (σ j).1 := fun j => (hsect j).1

  let ε : Fin (nearCard 𝔛reg.width v n) ⊕ Fin (farCard 𝔛reg.width v n) ≃ Fin m := nearFarEquiv 𝔛reg.width v n

  let q : Fin (farCard 𝔛reg.width v n) → ↥(DRModelPackage.XO p O) := fun i =>
    𝔛reg.toDR.base (((σ (ε (Sum.inr i))).1).base (IsLocalRing.closedPoint O))
  have hq_closed : ∀ i, IsClosed ({q i} : Set ↥(DRModelPackage.XO p O)) := fun i =>
    isClosed_singleton_toDR_closedPoint (σ (ε (Sum.inr i))) (hv _).1
  have hq_ne : ∀ i, q i ≠ 𝔛reg.crossingPt n := fun i =>
    toDR_closedPoint_ne_crossingPt_of_forall_ne_inr 𝒞 hϖ hF n (σ (ε (Sum.inr i))) (v (ε (Sum.inr i))) (hv _)
      (fun k => v_nearFarEquiv_inr_ne 𝔛reg.width v n i k)
  obtain ⟨V₀, hxV₀, hV₀U, hqV₀⟩ := AlgebraicGeometry.exists_open_subset_forall_notMem (𝒞.U n) (𝔛reg.crossingPt n)
    (𝒞.mem_U n) q hq_closed hq_ne

  let Vf : 𝔛reg.node → (DRModelPackage.XO p O).Opens := Function.update 𝒞.U n V₀
  have hVf : ∀ n', Vf n' ≤ 𝒞.U n' := by
    intro n'; by_cases h : n' = n
    · subst h; simp only [Vf, Function.update_self]; exact hV₀U
    · simp only [Vf, Function.update_of_ne h]; exact le_rfl
  have hxVf : ∀ n', 𝔛reg.crossingPt n' ∈ Vf n' := by
    intro n'; by_cases h : n' = n
    · subst h; simp only [Vf, Function.update_self]; exact hxV₀
    · simp only [Vf, Function.update_of_ne h]; exact 𝒞.mem_U n'
  let 𝒞' : 𝔛reg.ChartWitness ϖ Fc := 𝒞.restrict Vf hVf hxVf
  have hU' : 𝒞'.U n = V₀ := by
    show (𝒞.restrict Vf hVf hxVf).U n = V₀
    rw [restrict_U]; simp only [Vf, Function.update_self]

  haveI := DRModelPackage.isSeparated_snd_toBase 𝔛 O
  have hedge := 𝔛reg.edgePt_zero_mem_preimage_toDR n (𝒞'.U n) (𝒞'.mem_U n)
  haveI : IsIntegral (pullback (𝒞'.f n) (Resolution.toCrossing ϖ (𝔛reg.width n))) :=
    𝔛reg.isIntegral_pullback_of_iso_preimage_toDR (𝒞'.U n) (𝒞'.f n) (Resolution.toCrossing ϖ (𝔛reg.width n))
      (𝒞'.Φ n) _ hedge
  have hgen := 𝔛reg.exists_pullback_base_ne_closedPoint (𝒞'.U n) (𝒞'.f n) (Resolution.toCrossing ϖ (𝔛reg.width n))
    (𝒞'.Φ n) (𝒞'.Φ_fst n) _ hedge

  have hnear : ∀ i : Fin (nearCard 𝔛reg.width v n), ∃ σ' : Spec (CommRingCat.of O) ⟶
      pullback (𝒞'.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)),
      σ' ≫ ((𝒞'.Φ n).hom ≫ (𝔛reg.toDR ⁻¹ᵁ 𝒞'.U n).ι) = (σ (ε (Sum.inl i))).1 ∧
      σ' ≫ pullback.fst (𝒞'.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)) ≫ (𝒞'.U n).ι ≫
          pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) = 𝟙 _ ∧
      (σ'.base (IsLocalRing.closedPoint O) ∈
          ((Fc (𝔛reg.width n) ⟨(nearChainPos 𝔛reg.width v n i - 1) + 1, by
              have := nearChainPos_pos_and_lt 𝔛reg.width v n i; omega⟩).comap
            (pullback.snd (𝒞'.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)))).support ∧
        ∀ k : Fin (𝔛reg.width n + 1), (k : ℕ) ≠ (nearChainPos 𝔛reg.width v n i - 1) + 1 →
          σ'.base (IsLocalRing.closedPoint O) ∉
            ((Fc (𝔛reg.width n) k).comap (pullback.snd (𝒞'.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)))).support) := by
    intro i
    have hvi := v_nearFarEquiv_inl 𝔛reg.width v n i
    exact 𝒞'.exists_sectionLift n (σ (ε (Sum.inl i)))
      ⟨nearChainPos 𝔛reg.width v n i - 1, by have := nearChainPos_pos_and_lt 𝔛reg.width v n i; omega⟩
      ⟨by rw [← hvi]; exact (hv _).2.1, fun w hw => (hv _).2.2 w (by rw [hvi]; exact hw)⟩
  choose σ' hσ'ψ hσ'1 hσ'd using hnear

  let J : Fin (farCard 𝔛reg.width v n) → (pullback (𝒞'.f n) (Resolution.toCrossing ϖ (𝔛reg.width n))).IdealSheafData :=
    fun i => ((σ (ε (Sum.inr i))).1.ker).comap (𝒞'.ψ n)
  have hfar : ∀ i : Fin (farCard 𝔛reg.width v n), (J i).IsInvertible ∧
      (((J i).support : Set ↥(pullback (𝒞'.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)))) ∩
        (pullback.fst (𝒞'.f n) (Resolution.toCrossing ϖ (𝔛reg.width n)) ≫ (𝒞'.U n).ι ≫
          pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base ⁻¹'
            {IsLocalRing.closedPoint O} = ∅) := fun i =>
    𝒞'.farJ n (σ (ε (Sum.inr i))) (hsect _).2 (by rw [hU']; exact hqV₀ i)

  have hdj : ∀ j : Fin (nearCard 𝔛reg.width v n),
      nearChainPos 𝔛reg.width v n j - 1 + 1 = nearChainPos 𝔛reg.width v n j := fun j =>
    Nat.sub_add_cancel (nearChainPos_pos_and_lt 𝔛reg.width v n j).1
  have halpha : ∀ i : Fin (𝔛reg.width n - 1),
      (∑ j : Fin (nearCard 𝔛reg.width v n),
          if nearChainPos 𝔛reg.width v n j - 1 + 1 = (i : ℕ) + 1 then
            ((pos (ε (Sum.inl j)) : ℤ) - neg (ε (Sum.inl j))) else 0) +
        intersectionAlpha (x0MqResolvedTable 𝔛reg.width) (fun F => (aplus F : ℤ) - aminus F) (Sum.inr ⟨n, i⟩) = 0 := by
    intro i
    have h := hdeg n i
    rw [sum_single_inr_eq_sum_near 𝔛reg.width v n pos neg i] at h
    simp only [hdj]
    exact h

  obtain ⟨V, hxV, hVU', hτ⟩ := 𝒞'.descLoc_call hϖ n hgen hF σ' hσ'1
    (fun j => pos (ε (Sum.inl j))) (fun j => neg (ε (Sum.inl j)))
    (fun j => nearChainPos 𝔛reg.width v n j - 1 + 1)
    (fun j => by
      obtain ⟨h1, h2⟩ := nearChainPos_pos_and_lt 𝔛reg.width v n j
      show 0 < nearChainPos 𝔛reg.width v n j - 1 + 1 ∧ nearChainPos 𝔛reg.width v n j - 1 + 1 < 𝔛reg.width n
      constructor <;> omega)
    hσ'd J (fun i => (hfar i).1) (fun i => (hfar i).2)
    (fun i => pos (ε (Sum.inr i))) (fun i => neg (ε (Sum.inr i))) aplus aminus halpha

  have eT := 𝒞'.nonempty_pullback_ψ_divisorialSheaf_iso n (𝒞'.ψ n) rfl σ (fun j => (hsect j).2) pos neg aplus aminus ε σ'
    hσ'ψ (chainPos_injective 𝔛reg.width n)
    (fun F hFr => 𝔛reg.comap_comp_eq_top_of_forall_ne_chainPos n (𝒞'.U n) (fun m hm => 𝒞'.not_mem_U n m hm) (𝒞'.ψ n)
      (𝔛reg.toDR_base_mem_of_comp_ι (𝒞'.U n) (𝒞'.Φ n).hom) F (fun d hd => hFr ⟨d, hd.symm⟩))

  refine ⟨V, hxV, hVU'.trans (hU' ▸ hV₀U), ?_⟩
  exact 𝒞'.combine n _ _ eT V hVU' hτ

p2m_export "ModularCurve.DRResolvedModelPackage.ChartWitness" "exists_open_pullback_iso_unit"
end ChartWitness
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.IsNear"

end ModularCurve.DRResolvedModelPackage
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.IsNear"
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.IsNear"

theorem solution
    {p : ℕ} [Fact p.Prime] {𝔛 : DRModelPackage p}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ})
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
    {𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ}
    (Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ϖ e).IdealSheafData)
    (hF : ∀ (e : ℕ) (i : Fin e) (k : Fin (e + 1)), (Fc e k).comap (Resolution.ι ϖ e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O ϖ))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {CrossingQuotient.V ϖ}
          else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {CrossingQuotient.U ϖ} else ⊤)))
    (ch : 𝔛reg.DRResolvedModelCharts ϖ Fc)
    {m : ℕ} (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase) (pos neg : Fin m → ℕ)
    (v : Fin m → X0MqComponents 𝔛reg.width)
    (hv : ∀ j, (σ j).1.base (IsLocalRing.closedPoint O) ∈ 𝔛reg.smoothOffEdges ∧
        (σ j).1.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp (v j)).support ∧
        ∀ w, w ≠ v j → (σ j).1.base (IsLocalRing.closedPoint O) ∉ (𝔛reg.comp w).support)
    (aplus aminus : X0MqComponents 𝔛reg.width → ℕ)
    (hdeg : ∀ (nd : 𝔛reg.node) (i : Fin (𝔛reg.width nd - 1)),
        (∑ j, Finsupp.single (v j) ((pos j : ℤ) - (neg j : ℤ))) (Sum.inr ⟨nd, i⟩) +
          MazurRapoportAppendix.intersectionAlpha (x0MqResolvedTable 𝔛reg.width)
            (fun F => ((aplus F : ℤ) - (aminus F : ℤ))) (Sum.inr ⟨nd, i⟩) = 0)
    (n : 𝔛reg.node) :
    ∃ V : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Opens, 𝔛reg.crossingPt n ∈ V ∧ V ≤ ch.U n ∧
      Nonempty ((Scheme.Modules.pullback (𝔛reg.toDR ⁻¹ᵁ V).ι).obj
          ((List.finRange m).foldr
            (fun j N => ((σ j).1.ker ^ (pos j)).invModule ⊗ ((σ j).1.ker ^ (neg j)).module ⊗ N)
            ((∏ F, (𝔛reg.comp F) ^ (aplus F)).invModule ⊗ (∏ F, (𝔛reg.comp F) ^ (aminus F)).module)) ≅
        SheafOfModules.unit (𝔛reg.toDR ⁻¹ᵁ V).toScheme.ringCatSheaf) :=
  ModularCurve.DRResolvedModelPackage.ChartWitness.exists_open_pullback_iso_unit ch hϖ hF σ pos neg v hv aplus aminus hdeg n

end
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage.ChartWitness P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.DRResolvedModelPackage P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero.ModularCurve.IsNear"

end S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero
end P2MW
export P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero (solution)
