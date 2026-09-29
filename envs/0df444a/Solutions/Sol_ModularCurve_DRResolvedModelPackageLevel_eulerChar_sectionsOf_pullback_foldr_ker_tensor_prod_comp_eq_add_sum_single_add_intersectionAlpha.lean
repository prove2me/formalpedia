-- Prove2me | solution 1 for ModularCurve.DRResolvedModelPackageLevel.eulerChar_sectionsOf_pullback_foldr_ker_tensor_prod_comp_eq_add_sum_single_add_intersectionAlpha
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b6ceaf84-9e8e-5fb1-8783-b2703e26c071

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_pullback_foldr_pow_invModule_tensor_pow_module_tensor_eq_add_sum
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_pullback_finsetProd_pow_invModule_tensor_and_module_tensor
import Theorems.Thm_ModularCurve_DRResolvedModelPackageLevel_eulerChar_sectionsOf_pullback_pow_comp_invModule_tensor_and_module_tensor_self
import Theorems.Thm_ModularCurve_DRResolvedModelPackageLevel_eta_notMem_range_of_comp_toBase_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_comap_ker_eq_top_and_finrank_eq_zero_of_closedPoint_notMem_support
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_comap_ker_and_finrank_eq_one_of_mul_eq_span_natCast
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens
import Theorems.Thm_ModularCurve_intersectionAlpha_x0MqResolvedTable_eq_sum_x0MqAdj_and_sum_x0MqAdj_inl
import Theorems.Thm_ModularCurve_DRResolvedModelPackageLevel_isInvertible_comap_comp_subschemeIota
import Theorems.Thm_ModularCurve_DRResolvedModelPackageLevel_isFinite_and_finrank_subscheme_comap_comp_eq_natCard
import Theorems.Thm_ModularCurve_DRResolvedModelPackage_natCard_edge_eq_x0MqAdjV4
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRResolvedModelPackageLevel_eulerChar_sectionsOf_pullback_foldr_ker_tensor_prod_comp_eq_add_sum_single_add_intersectionAlpha
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection"

set_option autoImplicit false

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul
set_option maxHeartbeats 800000

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackageLevel_eulerChar_sectionsOf_pullback_foldr_ker_tensor_prod_comp_eq_add_sum_single_add_intersectionAlpha.ModularCurve NeronModelInfra MazurRapoportAppendix"
open scoped BigOperators

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRResolvedModelPackageLevel.chainPos DRResolvedModelPackageLevel DRModelPackageLevel.neZero_mul DRLevel.R DRModelPackageLevel X0MqComponents x0MqAdj x0MqAdj_symm x0MqResolvedTable DRResolvedModelPackageLevel.eulerChar_sectionsOf_pullback_pow_comp_invModule_tensor_and_module_tensor_self DRResolvedModelPackageLevel.eta_notMem_range_of_comp_toBase_eq_id intersectionAlpha_x0MqResolvedTable_eq_sum_x0MqAdj_and_sum_x0MqAdj_inl DRResolvedModelPackage DRResolvedModelPackageLevel.isInvertible_comap_comp_subschemeIota DRResolvedModelPackageLevel.isFinite_and_finrank_subscheme_comap_comp_eq_natCard DRResolvedModelPackage.natCard_edge_eq_x0MqAdjV4"
namespace E5W2aDeg
p2m_open "ModularCurve"

section Chi
variable {k : Type} [Field k] {Y : Scheme.{0}} (y : Y ⟶ Spec (CommRingCat.of k)) (𝒲 : Y.TwoAffineOpenCover)

private def chi (M : Y.Modules) : ℤ :=
  (Module.finrank k (𝒲.sectionsOf y M).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y M).H1

private theorem chi_def (M : Y.Modules) :
    chi y 𝒲 M = (Module.finrank k (𝒲.sectionsOf y M).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y M).H1 := rfl

private theorem cover_ext {X : Scheme.{0}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

private theorem chi_congr {M M' : Y.Modules} (e : M ≅ M') : chi y 𝒲 M = chi y 𝒲 M' := by
  obtain ⟨𝒱₂, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso y y (Iso.refl Y) (Category.id_comp y)
      𝒲 M' M (e ≪≫ ((Scheme.Modules.pullbackId Y).app M').symm)
  obtain rfl : 𝒱₂ = 𝒲 := cover_ext h0 h1
  rw [chi_def, chi_def, e0.finrank_eq, e1.finrank_eq]

private theorem nonempty_module_one_iso (X : Scheme.{0}) :
    Nonempty ((1 : X.IdealSheafData).module ≅ 𝟙_ X.Modules) := by
  have h1 : (1 : X.IdealSheafData).IsInvertible := by
    rw [Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top
  obtain ⟨em⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor h1 h1
  have e : (1 : X.IdealSheafData).module ≅ (1 : X.IdealSheafData).module ⊗ (1 : X.IdealSheafData).module :=
    eqToIso (congrArg Scheme.IdealSheafData.module (one_mul (1 : X.IdealSheafData)).symm) ≪≫ em
  have d : (1 : X.IdealSheafData).module ⊗ (1 : X.IdealSheafData).invModule ≅ 𝟙_ _ := (h1.isInvertible_module.dual).2.some
  exact ⟨(ρ_ _).symm ≪≫ whiskerLeftIso _ d.symm ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso e.symm _ ≪≫ d⟩
end Chi

private theorem chainPos_ne_succ {node : Type} (width : node → ℕ) (n : node) (d : ℕ) (hd : d < width n) :
    DRResolvedModelPackageLevel.chainPos width n d ≠ DRResolvedModelPackageLevel.chainPos width n (d + 1) := by
  unfold DRResolvedModelPackageLevel.chainPos
  by_cases h0 : d = 0
  · subst h0
    simp only [↓reduceDIte, Nat.zero_add, one_ne_zero]
    split_ifs with h <;> simp
  · simp only [h0, ↓reduceDIte, Nat.add_eq_zero_iff, one_ne_zero, and_false]
    by_cases h1 : d + 1 < width n
    · simp only [hd, ↓reduceDIte, h1, ne_eq, Sum.inr.injEq]
      intro h
      have := congrArg (fun q : Σ n, Fin (width n - 1) => (q.2 : ℕ)) h
      simp at this
      omega
    · simp [hd, h1]

private theorem x0MqAdj_self {node : Type} [Fintype node] [DecidableEq node] (e : node → ℕ) (i : X0MqComponents e) :
    x0MqAdj e i i = 0 := by
  cases i <;> simp [x0MqAdj]

section Pkg
variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} {𝔓 : DRModelPackageLevel N₀ p hpN₀} {O : Type} [CommRing O] {ρO : DRLevel.R p →+* O}
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ} (R : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)

private theorem eta_mem_support (w : X0MqComponents R.width) : R.η w ∈ (R.comp w).support := by
  obtain ⟨U, hU, hmax, -⟩ := R.η_stalk w
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hU, Scheme.mem_zeroLocus_iff]
  intro f hf hbo
  have hunit : IsUnit (R.Y.presheaf.germ (U : R.Y.Opens) (R.η w) hU f) := (R.Y.mem_basicOpen f (R.η w) hU).1 hbo
  have hmem : (R.Y.presheaf.germ (U : R.Y.Opens) (R.η w) hU).hom f ∈ IsLocalRing.maximalIdeal _ := by
    rw [← hmax]; exact Ideal.mem_map_of_mem _ hf
  exact (IsLocalRing.mem_maximalIdeal _).1 hmem hunit

private theorem not_mem_support_prod {x : R.Y} (s : Finset (X0MqComponents R.width))
    (h : ∀ w ∈ s, x ∉ (R.comp w).support) : x ∉ (∏ w ∈ s, R.comp w).support := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top]
    intro hx
    have hx' : x ∈ ((⊥ : TopologicalSpace.Closeds R.Y) : Set R.Y) := hx
    rw [TopologicalSpace.Closeds.coe_bot] at hx'
    exact hx'
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.IdealSheafData.support_mul]
    intro hx
    have hx' : x ∈ (((R.comp a).support ⊔ (∏ w ∈ s, R.comp w).support : TopologicalSpace.Closeds R.Y) : Set R.Y) := hx
    rw [TopologicalSpace.Closeds.coe_sup, Set.mem_union] at hx'
    rcases hx' with hx | hx
    · exact h a (Finset.mem_insert_self a s) hx
    · exact ih (fun w hw => h w (Finset.mem_insert_of_mem hw)) hx

private theorem isInvertible_prod_pow (s : Finset (X0MqComponents R.width)) (a : X0MqComponents R.width → ℕ) :
    (∏ w ∈ s, R.comp w ^ a w).IsInvertible := by
  refine Finset.prod_induction _ (fun J : R.Y.IdealSheafData => J.IsInvertible)
    (fun _ _ h h' => h.mul h') ?_ (fun i _ => (R.comp_isInvertible i).pow (a i))
  rw [Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top

private theorem ne_edgePt [IsLocalRing O] (σ : Spec (CommRingCat.of O) ⟶ R.Y) (v : X0MqComponents R.width)
    (hv : ∀ w, w ≠ v → σ.base (IsLocalRing.closedPoint O) ∉ (R.comp w).support)
    (n : R.node) (d : Fin (R.width n)) : σ.base (IsLocalRing.closedPoint O) ≠ R.edgePt n d := by
  intro h
  have hmem := R.edgePt_mem n d
  rw [← h] at hmem
  have h1 : DRResolvedModelPackageLevel.chainPos R.width n d = v := by
    by_contra hne; exact hv _ hne hmem.1
  have h2 : DRResolvedModelPackageLevel.chainPos R.width n (d + 1) = v := by
    by_contra hne; exact hv _ hne hmem.2
  exact chainPos_ne_succ R.width n d d.isLt (h1.trans h2.symm)

end Pkg

end ModularCurve.E5W2aDeg

end

open ModularCurve.E5W2aDeg in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} {𝔓 : DRModelPackageLevel N₀ p hpN₀}
    {O : Type} [CommRing O] [IsLocalRing O] {ρO : DRLevel.R p →+* O}
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ}
    (R : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)
    {m : ℕ} (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) R.toBase) (pos neg : Fin m → ℕ)
    (v : Fin m → X0MqComponents R.width)
    (hv : ∀ j, (σ j).1.base (IsLocalRing.closedPoint O) ∈ (R.comp (v j)).support ∧
      ∀ w, w ≠ v j → (σ j).1.base (IsLocalRing.closedPoint O) ∉ (R.comp w).support)
    (aplus aminus : X0MqComponents R.width → ℕ)
    (c : X0MqComponents R.width)
    {k : Type} [Field k] (y : (R.comp c).subscheme ⟶ Spec (CommRingCat.of k)) [IsProper y]
    (hrat : ∀ (n : R.node) (d : Fin (R.width n)), R.edgePt n d ∈ (R.comp c).support →
      ∃ s : Spec (CommRingCat.of k) ⟶ (R.comp c).subscheme,
        s ≫ y = 𝟙 _ ∧ R.edgePt n d ∈ Set.range (s ≫ (R.comp c).subschemeι).base)
    (hratσ : ∀ j, v j = c →
      ∃ s : Spec (CommRingCat.of k) ⟶ (R.comp c).subscheme,
        s ≫ y = 𝟙 _ ∧ (σ j).1.base (IsLocalRing.closedPoint O) ∈ Set.range (s ≫ (R.comp c).subschemeι).base)
    (𝒲 : ((R.comp c).subscheme).TwoAffineOpenCover) :
    (Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp c).subschemeι).obj
        ((List.finRange m).foldr
          (fun j N => (((σ j).1.ker) ^ (pos j)).invModule ⊗ (((σ j).1.ker) ^ (neg j)).module ⊗ N)
          ((∏ F, (R.comp F) ^ (aplus F)).invModule ⊗ (∏ F, (R.comp F) ^ (aminus F)).module)))).H0 : ℤ)
      - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp c).subschemeι).obj
        ((List.finRange m).foldr
          (fun j N => (((σ j).1.ker) ^ (pos j)).invModule ⊗ (((σ j).1.ker) ^ (neg j)).module ⊗ N)
          ((∏ F, (R.comp F) ^ (aplus F)).invModule ⊗ (∏ F, (R.comp F) ^ (aminus F)).module)))).H1
    = (Module.finrank k (𝒲.sectionsOf y (𝟙_ ((R.comp c).subscheme).Modules)).H0 : ℤ)
      - Module.finrank k (𝒲.sectionsOf y (𝟙_ ((R.comp c).subscheme).Modules)).H1
      + (∑ j, Finsupp.single (v j) ((pos j : ℤ) - (neg j : ℤ))) c
      + intersectionAlpha (x0MqResolvedTable R.width) (fun F => ((aplus F : ℤ) - (aminus F : ℤ))) c := by
  classical

  haveI : IsIntegral (R.comp c).subscheme := R.comp_integral c
  haveI : IsSeparated R.toBase := inferInstance
  have hci : ∀ j, IsClosedImmersion (σ j).1 := fun j => by
    have : IsClosedImmersion ((σ j).1 ≫ R.toBase) := by rw [(σ j).2]; infer_instance
    exact IsClosedImmersion.of_comp (σ j).1 R.toBase

  have hker : ∀ j, ((σ j).1.ker).IsInvertible := fun j =>
    Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens R.toBase R.smoothOffEdges (σ j).1 (σ j).2
      (R.mem_smoothOffEdges _ (ne_edgePt R (σ j).1 (v j) (hv j).2))

  let dj : Fin m → ℕ := fun j => if v j = c then 1 else 0
  have hdat : ∀ j, (((σ j).1.ker).comap (R.comp c).subschemeι).IsInvertible ∧
      IsFinite (((((σ j).1.ker).comap (R.comp c).subschemeι).subschemeι ≫ y)) ∧
      ∀ t : Spec (CommRingCat.of k), (((((σ j).1.ker).comap (R.comp c).subschemeι).subschemeι ≫ y)).finrank t = dj j := by
    intro j
    haveI := hci j
    by_cases hj : v j = c
    ·
      have hprod : ∀ U : R.Y.affineOpens,
          (R.comp c * ∏ w ∈ Finset.univ.erase c, R.comp w).ideal U = Ideal.span {((p : ℕ) : Γ(R.Y, U))} := by
        intro U
        rw [Finset.mul_prod_erase Finset.univ (fun w => R.comp w) (Finset.mem_univ c)]
        exact R.comp_prod U
      have hJ' : (σ j).1.base (IsLocalRing.closedPoint O) ∉ (∏ w ∈ Finset.univ.erase c, R.comp w).support :=
        not_mem_support_prod R _ (fun w hw => (hv j).2 w (by rw [hj]; exact Finset.ne_of_mem_erase hw))
      have hne : ∃ x ∈ (R.comp c).support, x ∉ Set.range (σ j).1.base :=
        ⟨R.η c, eta_mem_support R c,
          ModularCurve.DRResolvedModelPackageLevel.eta_notMem_range_of_comp_toBase_eq_id N₀ p hϖ R (σ j).1 (σ j).2 c⟩
      obtain ⟨h1, h2, h3⟩ :=
        Scheme.Hom.isInvertible_comap_ker_and_finrank_eq_one_of_mul_eq_span_natCast hϖ (σ j).1 (hker j)
          (R.comp c) (∏ w ∈ Finset.univ.erase c, R.comp w) hprod hJ' hne y (hratσ j hj)
      refine ⟨h1, h2, fun t => ?_⟩
      simp only [dj, hj, ↓reduceIte]
      exact h3 t
    · obtain ⟨-, h1, h2, h3⟩ :=
        Scheme.Hom.comap_ker_eq_top_and_finrank_eq_zero_of_closedPoint_notMem_support (σ j).1 (R.comp c)
          ((hv j).2 c (Ne.symm hj)) y
      refine ⟨h1, h2, fun t => ?_⟩
      simp only [dj, hj, ↓reduceIte]
      exact h3 t

  set Pp := ∏ F, R.comp F ^ aplus F with hPp
  set Pm := ∏ F, R.comp F ^ aminus F with hPm
  have hPpi : Pp.IsInvertible := isInvertible_prod_pow R _ _
  have hPmi : Pm.IsInvertible := isInvertible_prod_pow R _ _
  have hN : Scheme.Modules.IsInvertible (Pp.invModule ⊗ Pm.module) :=
    hPpi.isInvertible_invModule.tensor hPmi.isInvertible_module
  have hσpeel :=
    AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_pullback_foldr_pow_invModule_tensor_pow_module_tensor_eq_add_sum
      (R.comp c).subschemeι y (fun j => (σ j).1.ker) hker (fun j => (hdat j).1) dj (fun j => (hdat j).2.1)
      (fun j t => (hdat j).2.2 t) pos neg (Pp.invModule ⊗ Pm.module) hN 𝒲
  rw [← chi_def, ← chi_def] at hσpeel

  have hc := R.comp_isInvertible c
  set Pp' := ∏ F ∈ Finset.univ.erase c, R.comp F ^ aplus F with hPp'
  set Pm' := ∏ F ∈ Finset.univ.erase c, R.comp F ^ aminus F with hPm'
  have hPp'i : Pp'.IsInvertible := isInvertible_prod_pow R _ _
  have hPm'i : Pm'.IsInvertible := isInvertible_prod_pow R _ _
  have hsplitp : R.comp c ^ aplus c * Pp' = Pp := Finset.mul_prod_erase Finset.univ (fun F => R.comp F ^ aplus F) (Finset.mem_univ c)
  have hsplitm : R.comp c ^ aminus c * Pm' = Pm := Finset.mul_prod_erase Finset.univ (fun F => R.comp F ^ aminus F) (Finset.mem_univ c)
  obtain ⟨ep⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor (hc.pow (aplus c)) hPp'i
  obtain ⟨em⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor (hc.pow (aminus c)) hPm'i
  have eP : Pp.invModule ≅ (R.comp c ^ aplus c).invModule ⊗ Pp'.invModule :=
    eqToIso (congrArg Scheme.IdealSheafData.invModule hsplitp.symm) ≪≫ ep
  have eM : Pm.module ≅ (R.comp c ^ aminus c).module ⊗ Pm'.module :=
    eqToIso (congrArg Scheme.IdealSheafData.module hsplitm.symm) ≪≫ em

  have eN : Pp.invModule ⊗ Pm.module ≅
      (R.comp c ^ aplus c).invModule ⊗ (Pp'.invModule ⊗ ((R.comp c ^ aminus c).module ⊗ Pm'.module)) :=
    tensorIso eP eM ≪≫ α_ _ _ _
  have hM2 : Scheme.Modules.IsInvertible ((R.comp c ^ aminus c).module ⊗ Pm'.module) :=
    (hc.pow (aminus c)).isInvertible_module.tensor hPm'i.isInvertible_module
  have hM1 : Scheme.Modules.IsInvertible (Pp'.invModule ⊗ ((R.comp c ^ aminus c).module ⊗ Pm'.module)) :=
    hPp'i.isInvertible_invModule.tensor hM2

  have hratPL : ∀ F, F ≠ c → ∀ (n : R.node) (d : Fin (R.width n)),
      (F = DRResolvedModelPackageLevel.chainPos R.width n d ∧ c = DRResolvedModelPackageLevel.chainPos R.width n (d + 1)) ∨
        (c = DRResolvedModelPackageLevel.chainPos R.width n d ∧ F = DRResolvedModelPackageLevel.chainPos R.width n (d + 1)) →
      ∃ s : Spec (CommRingCat.of k) ⟶ (R.comp c).subscheme,
        s ≫ y = 𝟙 _ ∧ R.edgePt n d ∈ Set.range (s ≫ (R.comp c).subschemeι).base := by
    intro F _ n d h
    apply hrat n d
    rcases h with ⟨-, h2⟩ | ⟨h1, -⟩
    · rw [h2]; exact (R.edgePt_mem n d).2
    · rw [h1]; exact (R.edgePt_mem n d).1
  have hdegF : ∀ F ∈ Finset.univ.erase c, ∀ t : Spec (CommRingCat.of k),
      (((R.comp F).comap (R.comp c).subschemeι).subschemeι ≫ y).finrank t = x0MqAdj R.width F c := by
    intro F hF t
    have hFc := Finset.ne_of_mem_erase hF
    rw [(ModularCurve.DRResolvedModelPackageLevel.isFinite_and_finrank_subscheme_comap_comp_eq_natCard N₀ p R F c hFc y
      (hratPL F hFc)).2 t]
    exact ModularCurve.DRResolvedModelPackage.natCard_edge_eq_x0MqAdjV4 R.width F c hFc
  have hfinF : ∀ F ∈ Finset.univ.erase c, IsFinite ((((R.comp F).comap (R.comp c).subschemeι).subschemeι ≫ y)) :=
    fun F hF => (ModularCurve.DRResolvedModelPackageLevel.isFinite_and_finrank_subscheme_comap_comp_eq_natCard N₀ p R F c
      (Finset.ne_of_mem_erase hF) y (hratPL F (Finset.ne_of_mem_erase hF))).1
  have hinvF : ∀ F ∈ Finset.univ.erase c, ((R.comp F).comap (R.comp c).subschemeι).IsInvertible :=
    fun F hF => ModularCurve.DRResolvedModelPackageLevel.isInvertible_comap_comp_subschemeIota N₀ p R F c (Finset.ne_of_mem_erase hF)

  have hself1 := (ModularCurve.DRResolvedModelPackageLevel.eulerChar_sectionsOf_pullback_pow_comp_invModule_tensor_and_module_tensor_self
    N₀ p R c y hrat _ hM1 (aplus c) 𝒲).1

  have hoff1 := (AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_pullback_finsetProd_pow_invModule_tensor_and_module_tensor
    (R.comp c).subschemeι y (Finset.univ.erase c) R.comp aplus (fun F => x0MqAdj R.width F c)
    (fun F _ => R.comp_isInvertible F) hinvF hfinF hdegF _ hM2 𝒲).1

  have hself2 := (ModularCurve.DRResolvedModelPackageLevel.eulerChar_sectionsOf_pullback_pow_comp_invModule_tensor_and_module_tensor_self
    N₀ p R c y hrat _ hPm'i.isInvertible_module (aminus c) 𝒲).2

  have htop : (⊤ : R.Y.IdealSheafData).IsInvertible := Scheme.IdealSheafData.isInvertible_top
  have hoff2 := (AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_pullback_finsetProd_pow_invModule_tensor_and_module_tensor
    (R.comp c).subschemeι y (Finset.univ.erase c) R.comp aminus (fun F => x0MqAdj R.width F c)
    (fun F _ => R.comp_isInvertible F) hinvF hfinF hdegF _ htop.isInvertible_module 𝒲).2
  rw [← chi_def, ← chi_def] at hself1 hoff1 hself2 hoff2

  obtain ⟨e1⟩ := nonempty_module_one_iso R.Y
  have etop : (⊤ : R.Y.IdealSheafData).module ≅ 𝟙_ _ := eqToIso (congrArg Scheme.IdealSheafData.module
    (Scheme.IdealSheafData.one_eq_top (X := R.Y)).symm) ≪≫ e1
  have hunit : chi y 𝒲 ((Scheme.Modules.pullback (R.comp c).subschemeι).obj (⊤ : R.Y.IdealSheafData).module) =
      chi y 𝒲 (𝟙_ _) :=
    chi_congr y 𝒲 ((Scheme.Modules.pullback _).mapIso etop ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _)
  have hPm'top : chi y 𝒲 ((Scheme.Modules.pullback (R.comp c).subschemeι).obj Pm'.module) =
      chi y 𝒲 ((Scheme.Modules.pullback (R.comp c).subschemeι).obj (Pm'.module ⊗ (⊤ : R.Y.IdealSheafData).module)) :=
    chi_congr y 𝒲 ((Scheme.Modules.pullback _).mapIso ((ρ_ _).symm ≪≫ whiskerLeftIso _ etop.symm))
  have hNchi : chi y 𝒲 ((Scheme.Modules.pullback (R.comp c).subschemeι).obj (Pp.invModule ⊗ Pm.module)) =
      chi y 𝒲 ((Scheme.Modules.pullback (R.comp c).subschemeι).obj
        ((R.comp c ^ aplus c).invModule ⊗ (Pp'.invModule ⊗ ((R.comp c ^ aminus c).module ⊗ Pm'.module)))) :=
    chi_congr y 𝒲 ((Scheme.Modules.pullback _).mapIso eN)

  have hsum : (∑ j, ((pos j : ℤ) - (neg j : ℤ)) * (dj j : ℤ)) = (∑ j, Finsupp.single (v j) ((pos j : ℤ) - (neg j : ℤ))) c := by
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finsupp.single_apply]
    by_cases hj : v j = c <;> simp [dj, hj]
  obtain ⟨halpha, -, -⟩ := ModularCurve.intersectionAlpha_x0MqResolvedTable_eq_sum_x0MqAdj_and_sum_x0MqAdj_inl R.width R.one_le_width
  have hα := halpha (fun F => ((aplus F : ℤ) - (aminus F : ℤ))) c
  have hsplit1 : (∑ F, ((aplus F : ℤ) - (aminus F : ℤ)) * (x0MqAdj R.width F c : ℤ)) =
      ∑ F ∈ Finset.univ.erase c, ((aplus F : ℤ) - (aminus F : ℤ)) * (x0MqAdj R.width F c : ℤ) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ c), x0MqAdj_self]; simp
  have hsplit2 : (∑ F, (x0MqAdj R.width c F : ℤ)) = ∑ F ∈ Finset.univ.erase c, (x0MqAdj R.width F c : ℤ) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ c), x0MqAdj_self]
    simp only [Nat.cast_zero, zero_add]
    exact Finset.sum_congr rfl (fun F _ => by rw [x0MqAdj_symm])

  rw [← chi_def, ← chi_def, hσpeel, hNchi, hself1, hoff1, hself2, hPm'top, hoff2, hunit, hsum, hα, hsplit1, hsplit2]
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

#print axioms solution

end S_ModularCurve_DRResolvedModelPackageLevel_eulerChar_sectionsOf_pullback_foldr_ker_tensor_prod_comp_eq_add_sum_single_add_intersectionAlpha
end P2MW
export P2MW.S_ModularCurve_DRResolvedModelPackageLevel_eulerChar_sectionsOf_pullback_foldr_ker_tensor_prod_comp_eq_add_sum_single_add_intersectionAlpha (solution)
