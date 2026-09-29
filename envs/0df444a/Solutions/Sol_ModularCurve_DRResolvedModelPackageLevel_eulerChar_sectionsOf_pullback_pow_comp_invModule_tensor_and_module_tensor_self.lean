-- Prove2me | solution 1 for ModularCurve.DRResolvedModelPackageLevel.eulerChar_sectionsOf_pullback_pow_comp_invModule_tensor_and_module_tensor_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/4e6ec43a-e3ad-5935-a12d-ff881546f4a6

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_pullback_finsetProd_pow_invModule_tensor_and_module_tensor
import Theorems.Thm_ModularCurve_DRResolvedModelPackageLevel_isInvertible_comap_comp_subschemeIota
import Theorems.Thm_ModularCurve_DRResolvedModelPackageLevel_isFinite_and_finrank_subscheme_comap_comp_eq_natCard
import Theorems.Thm_ModularCurve_DRResolvedModelPackage_natCard_edge_eq_x0MqAdjV4
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_nonempty_invModule_prod_pow_iso_tensorUnit_of_prod_pow_eq_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorUnit_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRResolvedModelPackageLevel_eulerChar_sectionsOf_pullback_pow_comp_invModule_tensor_and_module_tensor_self
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module"
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry ModularCurve NeronModelInfra MazurRapoportAppendix"
open scoped BigOperators

universe u

namespace E5W2aSelf

section chi
variable {k : Type u} [Field k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k)) (𝒲 : Y.TwoAffineOpenCover)

private noncomputable def chi (M : Y.Modules) : ℤ :=
  (Module.finrank k (𝒲.sectionsOf y M).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y M).H1

private theorem chi_def (M : Y.Modules) :
    chi y 𝒲 M = (Module.finrank k (𝒲.sectionsOf y M).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y M).H1 :=
  rfl

private theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

private theorem chi_congr {M M' : Y.Modules} (e : M ≅ M') : chi y 𝒲 M = chi y 𝒲 M' := by
  obtain ⟨𝒱₂, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso y y (Iso.refl Y) (Category.id_comp y)
      𝒲 M' M (e ≪≫ ((Scheme.Modules.pullbackId Y).app M').symm)
  obtain rfl : 𝒱₂ = 𝒲 := cover_ext h0 h1
  rw [chi_def, chi_def, e0.finrank_eq, e1.finrank_eq]

end chi

private theorem isInvertible_finsetProd {X : Scheme.{u}} {F : Type*} (S : Finset F) (I : F → X.IdealSheafData) (a : F → ℕ)
    (hI : ∀ i ∈ S, (I i).IsInvertible) : (∏ i ∈ S, I i ^ a i).IsInvertible := by
  refine Finset.prod_induction _ (fun J : X.IdealSheafData => J.IsInvertible)
    (fun _ _ h h' => h.mul h') ?_ (fun i hi => (hI i hi).pow (a i))
  rw [Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top

private theorem nonempty_invModule_iso_module {X : Scheme.{u}} {I Q C : X.IdealSheafData}
    (hQ : Q.IsInvertible) (hC : C.IsInvertible) (hIQC : Q * C = I)
    (eI : I.module ≅ 𝟙_ X.Modules) : Nonempty (C.invModule ≅ Q.module) := by
  obtain ⟨em⟩ := hQ.nonempty_mul_module_iso_tensor hC
  obtain ⟨⟨ec⟩, -⟩ := hC.nonempty_module_tensor_invModule_iso
  have e1 : I.module ≅ Q.module ⊗ C.module := eqToIso (by rw [hIQC]) ≪≫ em
  exact ⟨(λ_ _).symm ≪≫ whiskerRightIso (eI.symm ≪≫ e1) _ ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso _ ec ≪≫ ρ_ _⟩

private theorem nonempty_module_iso_invModule {X : Scheme.{u}} {I Q C : X.IdealSheafData}
    (hQ : Q.IsInvertible) (hC : C.IsInvertible) (hIQC : Q * C = I)
    (eI : I.invModule ≅ 𝟙_ X.Modules) : Nonempty (C.module ≅ Q.invModule) := by
  obtain ⟨em⟩ := hQ.nonempty_mul_invModule_iso_tensor hC
  obtain ⟨-, ⟨ec⟩⟩ := hC.nonempty_module_tensor_invModule_iso
  have e1 : I.invModule ≅ Q.invModule ⊗ C.invModule := eqToIso (by rw [hIQC]) ≪≫ em
  exact ⟨(λ_ _).symm ≪≫ whiskerRightIso (eI.symm ≪≫ e1) _ ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso _ ec ≪≫ ρ_ _⟩

private theorem nonempty_module_iso_unit_of_invModule {X : Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsInvertible)
    (e : I.invModule ≅ 𝟙_ X.Modules) : Nonempty (I.module ≅ 𝟙_ X.Modules) := by
  obtain ⟨⟨ec⟩, -⟩ := hI.nonempty_module_tensor_invModule_iso
  exact ⟨(ρ_ _).symm ≪≫ whiskerLeftIso _ e.symm ≪≫ ec⟩

private theorem prod_comp_pow_eq_ofIdealTop
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} {𝔓 : DRModelPackageLevel N₀ p hpN₀} {O : Type} [CommRing O] {ρO : DRLevel.R p →+* O}
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ} (R : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ) (a : ℕ) :
    (∏ F, R.comp F ^ a) = Scheme.IdealSheafData.ofIdealTop (Ideal.span {(((p : ℕ) : Γ(R.Y, ⊤)) ^ a)}) := by
  classical
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Finset.prod_pow, Scheme.IdealSheafData.ideal_pow, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span,
    Set.image_singleton, map_pow, map_natCast]
  show (∏ F, R.comp F).ideal U ^ a = _
  rw [R.comp_prod U, Ideal.span_singleton_pow]

private theorem nonempty_invModule_prod_comp_pow_iso_unit
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} {𝔓 : DRModelPackageLevel N₀ p hpN₀} {O : Type} [CommRing O] {ρO : DRLevel.R p →+* O}
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ} (R : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ) (a : ℕ) :
    Nonempty ((∏ F, R.comp F ^ a).invModule ≅ 𝟙_ R.Y.Modules) := by
  classical
  obtain ⟨t, -, ht⟩ := Scheme.Modules.exists_hom_tensorUnit_app_eq_smul (X := R.Y) (((p : ℕ) : Γ(R.Y, ⊤)) ^ a)
  have hZ := Scheme.Modules.zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul t _ ht
  exact Scheme.IdealSheafData.nonempty_invModule_prod_pow_iso_tensorUnit_of_prod_pow_eq_zeroSchemeIdeal
    R.comp R.comp_isInvertible (fun _ => a) t (by rw [hZ]; exact prod_comp_pow_eq_ofIdealTop N₀ p R a)

end E5W2aSelf

open E5W2aSelf in
set_option maxHeartbeats 3200000 in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} {𝔓 : DRModelPackageLevel N₀ p hpN₀}
    {O : Type} [CommRing O] {ρO : DRLevel.R p →+* O}
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ}
    (R : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)
    (c : X0MqComponents R.width)
    {k : Type} [Field k] (y : (R.comp c).subscheme ⟶ Spec (CommRingCat.of k)) [IsProper y]
    (hrat : ∀ (n : R.node) (d : Fin (R.width n)), R.edgePt n d ∈ (R.comp c).support →
      ∃ s : Spec (CommRingCat.of k) ⟶ (R.comp c).subscheme,
        s ≫ y = 𝟙 _ ∧ R.edgePt n d ∈ Set.range (s ≫ (R.comp c).subschemeι).base)
    (M : R.Y.Modules) (hM : Scheme.Modules.IsInvertible M) (a : ℕ) (𝒲 : ((R.comp c).subscheme).TwoAffineOpenCover) :
    ((Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp c).subschemeι).obj (((R.comp c) ^ a).invModule ⊗ M))).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp c).subschemeι).obj (((R.comp c) ^ a).invModule ⊗ M))).H1
      = (Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp c).subschemeι).obj M)).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp c).subschemeι).obj M)).H1
        - (a : ℤ) * ∑ F ∈ Finset.univ.erase c, (x0MqAdj R.width F c : ℤ)) ∧
    ((Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp c).subschemeι).obj (((R.comp c) ^ a).module ⊗ M))).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp c).subschemeι).obj (((R.comp c) ^ a).module ⊗ M))).H1
      = (Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp c).subschemeι).obj M)).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp c).subschemeι).obj M)).H1
        + (a : ℤ) * ∑ F ∈ Finset.univ.erase c, (x0MqAdj R.width F c : ℤ)) := by
  classical
  set S : Finset (X0MqComponents R.width) := Finset.univ.erase c with hS
  set ιc := (R.comp c).subschemeι with hιc
  have hne : ∀ F ∈ S, F ≠ c := fun F hF => Finset.ne_of_mem_erase hF

  have hI : ∀ F ∈ S, (R.comp F).IsInvertible := fun F _ => R.comp_isInvertible F
  have hIY : ∀ F ∈ S, ((R.comp F).comap ιc).IsInvertible := fun F hF =>
    ModularCurve.DRResolvedModelPackageLevel.isInvertible_comap_comp_subschemeIota N₀ p R F c (hne F hF)
  have hrat' : ∀ F : X0MqComponents R.width, ∀ (n : R.node) (d : Fin (R.width n)),
      (F = DRResolvedModelPackageLevel.chainPos R.width n d ∧ c = DRResolvedModelPackageLevel.chainPos R.width n (d + 1)) ∨
          (c = DRResolvedModelPackageLevel.chainPos R.width n d ∧ F = DRResolvedModelPackageLevel.chainPos R.width n (d + 1)) →
      ∃ s : Spec (CommRingCat.of k) ⟶ (R.comp c).subscheme,
        s ≫ y = 𝟙 _ ∧ R.edgePt n d ∈ Set.range (s ≫ (R.comp c).subschemeι).base := by
    intro F n d h
    apply hrat n d
    have hm := R.edgePt_mem n d
    rcases h with ⟨-, hc⟩ | ⟨hc, -⟩
    · rw [hc]; exact hm.2
    · rw [hc]; exact hm.1
  have hZd := fun F (hF : F ∈ S) =>
    ModularCurve.DRResolvedModelPackageLevel.isFinite_and_finrank_subscheme_comap_comp_eq_natCard N₀ p R F c (hne F hF) y (hrat' F)
  have hZ : ∀ F ∈ S, IsFinite ((((R.comp F).comap ιc).subschemeι) ≫ y) := fun F hF => (hZd F hF).1
  have hdeg : ∀ F ∈ S, ∀ t : Spec (CommRingCat.of k),
      ((((R.comp F).comap ιc).subschemeι) ≫ y).finrank t = x0MqAdj R.width F c := fun F hF t => by
    rw [(hZd F hF).2 t]
    exact ModularCurve.DRResolvedModelPackage.natCard_edge_eq_x0MqAdjV4 R.width F c (hne F hF)

  obtain ⟨key1, key2⟩ :=
    Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_pullback_finsetProd_pow_invModule_tensor_and_module_tensor
      ιc y S R.comp (fun _ => a) (fun F => x0MqAdj R.width F c) hI hIY hZ hdeg M hM 𝒲

  have hQC : (∏ F ∈ S, R.comp F ^ a) * R.comp c ^ a = ∏ F, R.comp F ^ a :=
    Finset.prod_erase_mul _ _ (Finset.mem_univ c)
  have hQ : (∏ F ∈ S, R.comp F ^ a).IsInvertible := isInvertible_finsetProd S R.comp (fun _ => a) hI
  have hC : (R.comp c ^ a).IsInvertible := (R.comp_isInvertible c).pow a
  have hP : (∏ F, R.comp F ^ a).IsInvertible := by rw [← hQC]; exact hQ.mul hC
  obtain ⟨eP⟩ := nonempty_invModule_prod_comp_pow_iso_unit N₀ p R a
  obtain ⟨eP'⟩ := nonempty_module_iso_unit_of_invModule hP eP
  obtain ⟨iso1⟩ := nonempty_invModule_iso_module hQ hC hQC eP'
  obtain ⟨iso2⟩ := nonempty_module_iso_invModule hQ hC hQC eP

  refine ⟨?_, ?_⟩
  · have h := chi_congr y 𝒲 ((Scheme.Modules.pullback ιc).mapIso (whiskerRightIso iso1 M))
    rw [chi_def, chi_def] at h
    rw [h, key2]
    simp only [Finset.mul_sum]
  · have h := chi_congr y 𝒲 ((Scheme.Modules.pullback ιc).mapIso (whiskerRightIso iso2 M))
    rw [chi_def, chi_def] at h
    rw [h, key1]
    simp only [Finset.mul_sum]

#print axioms solution

end S_ModularCurve_DRResolvedModelPackageLevel_eulerChar_sectionsOf_pullback_pow_comp_invModule_tensor_and_module_tensor_self
end P2MW
export P2MW.S_ModularCurve_DRResolvedModelPackageLevel_eulerChar_sectionsOf_pullback_pow_comp_invModule_tensor_and_module_tensor_self (solution)
