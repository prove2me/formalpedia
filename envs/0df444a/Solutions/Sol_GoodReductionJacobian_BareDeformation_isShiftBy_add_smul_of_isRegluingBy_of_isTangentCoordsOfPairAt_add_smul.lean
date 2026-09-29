-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/fa908c7b-2e63-50e8-95c5-4174237c39d7

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_MvFormalGroup_IsShiftBy
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_of_isRegluingBy_of_isPullback
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_overlap_isos_comap_of_sections
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_cocycle_of_isRegluingBy
import Theorems.Thm_GoodReductionJacobian_BareDeformation_appTop_eq_add_mul_sub_of_slices
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add_smul_of_apply_eq_add_mul_sub
import Theorems.Thm_AlgebraicGeometry_specMap_comp_fromSpec_eq_specMap_comp_of_morphismRestrict_comp_eq
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isPullback_isFormalCoordinates_map_of_ringHom_comp_eq
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_glued_scheme_of_overlap_isos
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_relativeGroupLaw_of_isPullback_of_smooth
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_deformation_isFormalCoordinates_liftsCoordinates
import Theorems.Thm_GoodReductionJacobian_BareDeformation_isIso_of_isRegluingBy_of_forall_comp_hom_eq
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_iso_one_comp_eq_mapPt_mul_of_isIso
import Theorems.Thm_GoodReductionJacobian_BareDeformation_isFormalCoordinates_and_liftsCoordinates_mapPt_inv
import Theorems.Thm_GoodReductionJacobian_BareDeformation_isIso_of_isFormalCoordinates_of_liftsCoordinates
import Theorems.Thm_MvFormalGroup_Deformation_isShiftBy_of_isIso_of_isIso
import Theorems.Thm_MvFormalGroup_Deformation_isIso_equivalence
import Theorems.Thm_MvFormalGroup_Deformation_isShiftBy_add_smul_of_toPowerSeries_eq_add_smul_sub
import Theorems.Thm_GoodReductionJacobian_BareDeformation_isShiftBy_of_isShiftBy_of_isRegluingBy_of_exists_d_eq_sub
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec GoodReductionJacobian.prodInr_comp_prodFst GoodReductionJacobian.RelativeGroupLaw.prod_inv GoodReductionJacobian.prodInl_comp_prodSnd GoodReductionJacobian.prodInr_comp_prodSnd GoodReductionJacobian.prodInl_comp_prodFst GoodReductionJacobian.prodFstPt_prodPairPt GoodReductionJacobian.prodFst_coe GoodReductionJacobian.prodSndPt_prodPairPt GoodReductionJacobian.RelativeGroupLaw.prod_one GoodReductionJacobian.prodPairPt_coe GoodReductionJacobian.prodPairPt_prodFstPt_prodSndPt GoodReductionJacobian.prodFstPt_coe GoodReductionJacobian.RelativeGroupLaw.prod_mul GoodReductionJacobian.prodSndPt_coe GoodReductionJacobian.prodSnd_coe AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover"

open scoped Quaternion TensorProduct NumberField

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw.FormalCoordinates RelativeGroupLaw AbelianSchemePropertyBundle BareDeformation RelativeGroupLaw.baseChange BareDeformation.exists_isRegluingBy_of_isRegluingBy_of_isPullback BareDeformation.exists_overlap_isos_comap_of_sections BareDeformation.exists_cocycle_of_isRegluingBy BareDeformation.appTop_eq_add_mul_sub_of_slices BareDeformation.exists_isPullback_isFormalCoordinates_map_of_ringHom_comp_eq BareDeformation.exists_glued_scheme_of_overlap_isos BareDeformation.exists_relativeGroupLaw_of_isPullback_of_smooth BareDeformation.exists_deformation_isFormalCoordinates_liftsCoordinates BareDeformation.isIso_of_isRegluingBy_of_forall_comp_hom_eq BareDeformation.exists_iso_one_comp_eq_mapPt_mul_of_isIso BareDeformation.isFormalCoordinates_and_liftsCoordinates_mapPt_inv BareDeformation.isIso_of_isFormalCoordinates_of_liftsCoordinates BareDeformation.isShiftBy_of_isShiftBy_of_isRegluingBy_of_exists_d_eq_sub"
namespace P2mTripleRing
p2m_open "GoodReductionJacobian"

variable (B B₁ : Type) [CommRing B] [CommRing B₁] [Algebra B B₁]

def tri : Subring (B × B × B) where
  carrier := {x | algebraMap B B₁ x.1 = algebraMap B B₁ x.2.1 ∧ algebraMap B B₁ x.2.1 = algebraMap B B₁ x.2.2}
  mul_mem' := by
    rintro x y ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
    refine ⟨?_, ?_⟩ <;> simp only [Prod.fst_mul, Prod.snd_mul, map_mul, hx₁, hx₂, hy₁, hy₂]
  one_mem' := ⟨by simp, by simp⟩
  add_mem' := by
    rintro x y ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
    refine ⟨?_, ?_⟩ <;> simp only [Prod.fst_add, Prod.snd_add, map_add, hx₁, hx₂, hy₁, hy₂]
  zero_mem' := ⟨by simp, by simp⟩
  neg_mem' := by
    rintro x ⟨hx₁, hx₂⟩
    refine ⟨?_, ?_⟩ <;> simp only [Prod.fst_neg, Prod.snd_neg, map_neg, hx₁, hx₂]

abbrev T : Type := ↥(tri B B₁)

def p₀ : T B B₁ →+* B := (RingHom.fst B (B × B)).comp (tri B B₁).subtype
def p₁ : T B B₁ →+* B := ((RingHom.fst B B).comp (RingHom.snd B (B × B))).comp (tri B B₁).subtype
def p₂ : T B B₁ →+* B := ((RingHom.snd B B).comp (RingHom.snd B (B × B))).comp (tri B B₁).subtype

@[scoped simp] theorem p₀_apply (x : T B B₁) : p₀ B B₁ x = x.1.1 := rfl
@[scoped simp] theorem p₁_apply (x : T B B₁) : p₁ B B₁ x = x.1.2.1 := rfl
@[scoped simp] theorem p₂_apply (x : T B B₁) : p₂ B B₁ x = x.1.2.2 := rfl

theorem mem_tri (x : B × B × B) :
    x ∈ tri B B₁ ↔ algebraMap B B₁ x.1 = algebraMap B B₁ x.2.1 ∧ algebraMap B B₁ x.2.1 = algebraMap B B₁ x.2.2 := Iff.rfl

def δ : B →+* T B B₁ :=
  ((RingHom.id B).prod ((RingHom.id B).prod (RingHom.id B))).codRestrict (tri B B₁) (fun _ => ⟨rfl, rfl⟩)

@[scoped simp] theorem δ_apply_coe (b : B) : (δ B B₁ b : B × B × B) = (b, b, b) := rfl

theorem p₀_comp_δ : (p₀ B B₁).comp (δ B B₁) = RingHom.id B := RingHom.ext fun _ => rfl
theorem p₁_comp_δ : (p₁ B B₁).comp (δ B B₁) = RingHom.id B := RingHom.ext fun _ => rfl
theorem p₂_comp_δ : (p₂ B B₁).comp (δ B B₁) = RingHom.id B := RingHom.ext fun _ => rfl

theorem ext_of_p {x y : T B B₁} (h₀ : p₀ B B₁ x = p₀ B B₁ y) (h₁ : p₁ B B₁ x = p₁ B B₁ y) (h₂ : p₂ B B₁ x = p₂ B B₁ y) :
    x = y :=
  Subtype.ext (Prod.ext h₀ (Prod.ext h₁ h₂))

theorem exists_of_congr (b₀ b₁ b₂ : B) (h₁ : algebraMap B B₁ b₀ = algebraMap B B₁ b₁) (h₂ : algebraMap B B₁ b₁ = algebraMap B B₁ b₂) :
    ∃ x : T B B₁, p₀ B B₁ x = b₀ ∧ p₁ B B₁ x = b₁ ∧ p₂ B B₁ x = b₂ :=
  ⟨⟨(b₀, b₁, b₂), h₁, h₂⟩, rfl, rfl, rfl⟩

scoped instance algebraB₁ : Algebra (T B B₁) B₁ := ((algebraMap B B₁).comp (p₀ B B₁)).toAlgebra

theorem algebraMap_eq : algebraMap (T B B₁) B₁ = (algebraMap B B₁).comp (p₀ B B₁) := rfl

theorem comp_p₀ : (algebraMap B B₁).comp (p₀ B B₁) = algebraMap (T B B₁) B₁ := rfl
theorem comp_p₁ : (algebraMap B B₁).comp (p₁ B B₁) = algebraMap (T B B₁) B₁ :=
  RingHom.ext fun x => by rw [algebraMap_eq]; exact x.2.1.symm
theorem comp_p₂ : (algebraMap B B₁).comp (p₂ B B₁) = algebraMap (T B B₁) B₁ :=
  RingHom.ext fun x => by rw [algebraMap_eq]; exact (x.2.1.trans x.2.2).symm
theorem comp_δ : (algebraMap (T B B₁) B₁).comp (δ B B₁) = algebraMap B B₁ := rfl

theorem sub_mem_ker₁ (x : T B B₁) : p₁ B B₁ x - p₀ B B₁ x ∈ RingHom.ker (algebraMap B B₁) := by
  rw [RingHom.mem_ker, map_sub, sub_eq_zero]; exact x.2.1.symm
theorem sub_mem_ker₂ (x : T B B₁) : p₂ B B₁ x - p₀ B B₁ x ∈ RingHom.ker (algebraMap B B₁) := by
  rw [RingHom.mem_ker, map_sub, sub_eq_zero]; exact (x.2.1.trans x.2.2).symm

def α (al : B) (hJ : ∀ j j' : B, j ∈ RingHom.ker (algebraMap B B₁) → j' ∈ RingHom.ker (algebraMap B B₁) → j * j' = 0) :
    T B B₁ →+* B where
  toFun x := p₁ B B₁ x + al * (p₂ B B₁ x - p₀ B B₁ x)
  map_one' := by simp
  map_mul' x y := by
    have e₁ := sub_mem_ker₁ B B₁ x; have e₂ := sub_mem_ker₂ B B₁ x
    have f₁ := sub_mem_ker₁ B B₁ y; have f₂ := sub_mem_ker₂ B B₁ y

    set x₀ := p₀ B B₁ x; set x₁ := p₁ B B₁ x; set x₂ := p₂ B B₁ x
    set y₀ := p₀ B B₁ y; set y₁ := p₁ B B₁ y; set y₂ := p₂ B B₁ y
    simp only [map_mul]

    have k1 : (x₂ - x₀) * (y₂ - y₀) = 0 := hJ _ _ e₂ f₂
    have k2 : (x₂ - x₁) * (y₂ - y₀) = 0 := by
      have : x₂ - x₁ = (x₂ - x₀) - (x₁ - x₀) := by ring
      rw [this, sub_mul, hJ _ _ e₂ f₂, hJ _ _ e₁ f₂, sub_zero]
    have k3 : (x₂ - x₀) * (y₀ - y₁) = 0 := by
      have : y₀ - y₁ = -(y₁ - y₀) := by ring
      rw [this, mul_neg, hJ _ _ e₂ f₁, neg_zero]
    have key : x₂ * y₂ - x₀ * y₀ = x₁ * (y₂ - y₀) + (x₂ - x₀) * y₁ := by
      have : x₂ * y₂ - x₀ * y₀ - (x₁ * (y₂ - y₀) + (x₂ - x₀) * y₁) = (x₂ - x₁) * (y₂ - y₀) + (x₂ - x₀) * (y₀ - y₁) := by ring
      rw [k2, k3, add_zero, sub_eq_zero] at this
      exact this
    rw [key]
    linear_combination (-(al ^ 2)) * k1
  map_zero' := by simp
  map_add' x y := by simp only [map_add]; ring

theorem α_apply (al : B) (hJ : ∀ j j' : B, j ∈ RingHom.ker (algebraMap B B₁) → j' ∈ RingHom.ker (algebraMap B B₁) → j * j' = 0)
    (x : T B B₁) : α B B₁ al hJ x = p₁ B B₁ x + al * (p₂ B B₁ x - p₀ B B₁ x) := rfl

theorem α_comp_δ (al : B) (hJ : ∀ j j' : B, j ∈ RingHom.ker (algebraMap B B₁) → j' ∈ RingHom.ker (algebraMap B B₁) → j * j' = 0) :
    (α B B₁ al hJ).comp (δ B B₁) = RingHom.id B :=
  RingHom.ext fun b => by simp [α_apply]

theorem comp_α (al : B) (hJ : ∀ j j' : B, j ∈ RingHom.ker (algebraMap B B₁) → j' ∈ RingHom.ker (algebraMap B B₁) → j * j' = 0) :
    (algebraMap B B₁).comp (α B B₁ al hJ) = algebraMap (T B B₁) B₁ :=
  RingHom.ext fun x => by
    rw [RingHom.comp_apply, α_apply, map_add, map_mul, (RingHom.mem_ker).mp (sub_mem_ker₂ B B₁ x), mul_zero, add_zero,
      algebraMap_eq, RingHom.comp_apply]
    exact x.2.1.symm

theorem p₀_surjective : Function.Surjective (p₀ B B₁) := fun b => ⟨δ B B₁ b, rfl⟩

theorem isUnit_of_isUnit_p₀ (hker : IsNilpotent (RingHom.ker (algebraMap B B₁))) (x : T B B₁) (hx : IsUnit (p₀ B B₁ x)) :
    IsUnit x := by
  obtain ⟨n, hn⟩ := hker
  have hn' : RingHom.ker (algebraMap B B₁) ^ (n + 1) = ⊥ := by rw [pow_succ, hn, zero_mul, Submodule.zero_eq_bot]

  have hm : IsNilpotent (x - δ B B₁ (p₀ B B₁ x)) := by
    refine ⟨n + 1, ext_of_p B B₁ ?_ ?_ ?_⟩
    · simp
    · rw [map_pow, map_zero]
      have h1 : p₁ B B₁ (x - δ B B₁ (p₀ B B₁ x)) ∈ RingHom.ker (algebraMap B B₁) := by
        simp only [map_sub]; exact sub_mem_ker₁ B B₁ x
      have := Ideal.pow_mem_pow h1 (n + 1)
      rw [hn'] at this
      exact (Submodule.mem_bot B).mp this
    · rw [map_pow, map_zero]
      have h2 : p₂ B B₁ (x - δ B B₁ (p₀ B B₁ x)) ∈ RingHom.ker (algebraMap B B₁) := by
        simp only [map_sub]; exact sub_mem_ker₂ B B₁ x
      have := Ideal.pow_mem_pow h2 (n + 1)
      rw [hn'] at this
      exact (Submodule.mem_bot B).mp this
  obtain ⟨u, hu⟩ := hx
  have hδu : IsUnit (δ B B₁ (p₀ B B₁ x)) := by rw [← hu]; exact u.isUnit.map (δ B B₁)
  have : x = δ B B₁ (p₀ B B₁ x) + (x - δ B B₁ (p₀ B B₁ x)) := by ring
  rw [this]
  obtain ⟨v, hv⟩ := hδu
  rw [← hv, show (↑v : T B B₁) + (x - ↑v) = ↑v * (1 + ↑v⁻¹ * (x - ↑v)) by
    rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]]
  refine (Units.isUnit v).mul ?_
  rw [add_comm]
  exact (Commute.all _ _).isNilpotent_mul_left (by rwa [hv]) |>.isUnit_add_one

theorem isLocalRing [IsLocalRing B] (hker : IsNilpotent (RingHom.ker (algebraMap B B₁))) : IsLocalRing (T B B₁) := by
  haveI : Nontrivial (T B B₁) :=
    nontrivial_of_ne (0 : T B B₁) 1 fun h => (zero_ne_one (α := B)) (by simpa using congrArg (p₀ B B₁) h)
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (p₀ B B₁ x) with h | h
  · exact Or.inl (isUnit_of_isUnit_p₀ B B₁ hker x h)
  · exact Or.inr (isUnit_of_isUnit_p₀ B B₁ hker (1 - x) (by simpa using h))

theorem surjective_algebraMap (hπ : Function.Surjective (algebraMap B B₁)) : Function.Surjective (algebraMap (T B B₁) B₁) := by
  rw [algebraMap_eq]; exact hπ.comp (p₀_surjective B B₁)

theorem p_mem_ker (x : T B B₁) (hx : x ∈ RingHom.ker (algebraMap (T B B₁) B₁)) :
    p₀ B B₁ x ∈ RingHom.ker (algebraMap B B₁) ∧ p₁ B B₁ x ∈ RingHom.ker (algebraMap B B₁) ∧
      p₂ B B₁ x ∈ RingHom.ker (algebraMap B B₁) := by
  rw [RingHom.mem_ker, algebraMap_eq, RingHom.comp_apply] at hx
  refine ⟨hx, ?_, ?_⟩
  · rw [RingHom.mem_ker, p₁_apply, ← x.2.1]; exact hx
  · rw [RingHom.mem_ker, p₂_apply, ← x.2.2, ← x.2.1]; exact hx

theorem isNilpotent_ker (hker : IsNilpotent (RingHom.ker (algebraMap B B₁))) :
    IsNilpotent (RingHom.ker (algebraMap (T B B₁) B₁)) := by
  obtain ⟨n, hn⟩ := hker
  have hle : ∀ (q : T B B₁ →+* B), (∀ x ∈ RingHom.ker (algebraMap (T B B₁) B₁), q x ∈ RingHom.ker (algebraMap B B₁)) →
      RingHom.ker (algebraMap (T B B₁) B₁) ^ n ≤ RingHom.ker q := by
    intro q hq
    have h1 : RingHom.ker (algebraMap (T B B₁) B₁) ≤ (RingHom.ker (algebraMap B B₁)).comap q := fun x hx => hq x hx
    calc RingHom.ker (algebraMap (T B B₁) B₁) ^ n ≤ ((RingHom.ker (algebraMap B B₁)).comap q) ^ n := Ideal.pow_right_mono h1 n
      _ ≤ ((RingHom.ker (algebraMap B B₁)) ^ n).comap q := Ideal.le_comap_pow q n
      _ = RingHom.ker q := by rw [hn, Submodule.zero_eq_bot, ← RingHom.ker_eq_comap_bot]
  refine ⟨n, ?_⟩
  rw [Submodule.zero_eq_bot, eq_bot_iff]
  intro x hx
  have h0 := hle (p₀ B B₁) (fun x hx => (p_mem_ker B B₁ x hx).1) hx
  have h1 := hle (p₁ B B₁) (fun x hx => (p_mem_ker B B₁ x hx).2.1) hx
  have h2 := hle (p₂ B B₁) (fun x hx => (p_mem_ker B B₁ x hx).2.2) hx
  rw [RingHom.mem_ker] at h0 h1 h2
  exact (Submodule.mem_bot _).mpr (ext_of_p B B₁ (by simpa using h0) (by simpa using h1) (by simpa using h2))

theorem isLocalHom_p₀ (hker : IsNilpotent (RingHom.ker (algebraMap B B₁))) : IsLocalHom (p₀ B B₁) :=
  ⟨fun x hx => isUnit_of_isUnit_p₀ B B₁ hker x hx⟩

theorem mem_maximalIdeal_iff [IsLocalRing B] (hker : IsNilpotent (RingHom.ker (algebraMap B B₁))) (x : T B B₁) :
    letI := isLocalRing B B₁ hker
    x ∈ maximalIdeal (T B B₁) ↔ p₀ B B₁ x ∈ maximalIdeal B := by
  letI := isLocalRing B B₁ hker
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  exact ⟨fun h => h.map _, isUnit_of_isUnit_p₀ B B₁ hker x⟩

theorem ker_mul_maximalIdeal [IsLocalRing B] (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B) (hsmall : RingHom.ker (algebraMap B B₁) * maximalIdeal B = ⊥) :
    letI := isLocalRing B B₁ hker
    RingHom.ker (algebraMap (T B B₁) B₁) * maximalIdeal (T B B₁) = ⊥ := by
  letI := isLocalRing B B₁ hker
  rw [eq_bot_iff, Ideal.mul_le]
  intro k hk m hm
  obtain ⟨hk0, hk1, hk2⟩ := p_mem_ker B B₁ k hk
  have hm0 : p₀ B B₁ m ∈ maximalIdeal B := (mem_maximalIdeal_iff B B₁ hker m).mp hm
  have hm1 : p₁ B B₁ m ∈ maximalIdeal B := by
    have : p₁ B B₁ m = p₀ B B₁ m + (p₁ B B₁ m - p₀ B B₁ m) := by ring
    rw [this]; exact Ideal.add_mem _ hm0 (hI (sub_mem_ker₁ B B₁ m))
  have hm2 : p₂ B B₁ m ∈ maximalIdeal B := by
    have : p₂ B B₁ m = p₀ B B₁ m + (p₂ B B₁ m - p₀ B B₁ m) := by ring
    rw [this]; exact Ideal.add_mem _ hm0 (hI (sub_mem_ker₂ B B₁ m))
  have hz : ∀ a b : B, a ∈ RingHom.ker (algebraMap B B₁) → b ∈ maximalIdeal B → a * b = 0 := fun a b ha hb => by
    have := Ideal.mul_mem_mul ha hb; rwa [hsmall, Ideal.mem_bot] at this
  exact (Submodule.mem_bot _).mpr (ext_of_p B B₁ (by simpa using hz _ _ hk0 hm0) (by simpa using hz _ _ hk1 hm1)
    (by simpa using hz _ _ hk2 hm2))

scoped instance algebraB : Algebra B (T B B₁) := (δ B B₁).toAlgebra

theorem moduleFinite [IsNoetherianRing B] : Module.Finite B (T B B₁) := by
  let f : T B B₁ →ₗ[B] (B × B × B) :=
    { toFun := Subtype.val
      map_add' := fun _ _ => rfl
      map_smul' := fun b x => by
        show ((δ B B₁ b * x : T B B₁) : B × B × B) = b • (x : B × B × B)
        rfl }
  exact Module.Finite.of_injective f Subtype.val_injective

theorem isArtinianRing [IsArtinianRing B] : IsArtinianRing (T B B₁) := by
  haveI : IsNoetherianRing B := inferInstance
  haveI := moduleFinite B B₁
  exact IsArtinianRing.of_finite B (T B B₁)

theorem residueField_map_bijective [IsLocalRing B] (hker : IsNilpotent (RingHom.ker (algebraMap B B₁))) :
    letI := isLocalRing B B₁ hker
    letI := isLocalHom_p₀ B B₁ hker
    Function.Bijective (IsLocalRing.ResidueField.map (p₀ B B₁)) := by
  letI := isLocalRing B B₁ hker
  letI := isLocalHom_p₀ B B₁ hker
  refine ⟨(IsLocalRing.ResidueField.map (p₀ B B₁)).injective, fun y => ?_⟩
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
  exact ⟨IsLocalRing.residue _ (δ B B₁ b), by rw [IsLocalRing.ResidueField.map_residue]; rfl⟩

theorem isAlgClosed_residueField [IsLocalRing B] [IsAlgClosed (IsLocalRing.ResidueField B)]
    (hker : IsNilpotent (RingHom.ker (algebraMap B B₁))) :
    letI := isLocalRing B B₁ hker
    IsAlgClosed (IsLocalRing.ResidueField (T B B₁)) := by
  letI := isLocalRing B B₁ hker
  letI := isLocalHom_p₀ B B₁ hker
  exact IsAlgClosed.of_ringEquiv (IsLocalRing.ResidueField B) _
    (RingEquiv.ofBijective (IsLocalRing.ResidueField.map (p₀ B B₁)) (residueField_map_bijective B B₁ hker)).symm

end GoodReductionJacobian.P2mTripleRing
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian.P2mTripleRing"
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw.FormalCoordinates RelativeGroupLaw AbelianSchemePropertyBundle BareDeformation RelativeGroupLaw.baseChange BareDeformation.exists_isRegluingBy_of_isRegluingBy_of_isPullback BareDeformation.exists_overlap_isos_comap_of_sections BareDeformation.exists_cocycle_of_isRegluingBy BareDeformation.appTop_eq_add_mul_sub_of_slices BareDeformation.exists_isPullback_isFormalCoordinates_map_of_ringHom_comp_eq BareDeformation.exists_glued_scheme_of_overlap_isos BareDeformation.exists_relativeGroupLaw_of_isPullback_of_smooth BareDeformation.exists_deformation_isFormalCoordinates_liftsCoordinates BareDeformation.isIso_of_isRegluingBy_of_forall_comp_hom_eq BareDeformation.exists_iso_one_comp_eq_mapPt_mul_of_isIso BareDeformation.isFormalCoordinates_and_liftsCoordinates_mapPt_inv BareDeformation.isIso_of_isFormalCoordinates_of_liftsCoordinates BareDeformation.isShiftBy_of_isShiftBy_of_isRegluingBy_of_exists_d_eq_sub"
namespace P2mKSComb
p2m_open "GoodReductionJacobian"

universe u

section Sections

variable {B' B B₁ : Type} [CommRing B'] [CommRing B] [CommRing B₁] [Algebra B' B₁] [Algebra B B₁]
  {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}

theorem exists_section (D₀ : BareDeformation f₁ L₁ B) (D₀' : BareDeformation f₁ L₁ B')
    (δ : B →+* B') (φ : B' →+* B) (hφδ : φ.comp δ = RingHom.id B) (hφ : (algebraMap B B₁).comp φ = algebraMap B' B₁)
    (h₀ : D₀'.A ⟶ D₀.A) (hc₀ : IsPullback h₀ D₀'.f D₀.f (Spec.map (CommRingCat.ofHom δ))) (hg₀ : D₀'.g ≫ h₀ = D₀.g) :
    ∃ k : D₀.A ⟶ D₀'.A, k ≫ h₀ = 𝟙 _ ∧ k ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom φ) ∧
      IsPullback k D₀.f D₀'.f (Spec.map (CommRingCat.ofHom φ)) ∧ D₀.g ≫ k = D₀'.g := by
  have hφδ' : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom δ) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφδ, CommRingCat.ofHom_id, Spec.map_id]
  have w : 𝟙 _ ≫ D₀.f = (D₀.f ≫ Spec.map (CommRingCat.ofHom φ)) ≫ Spec.map (CommRingCat.ofHom δ) := by
    rw [Category.assoc, hφδ', Category.id_comp, Category.comp_id]
  refine ⟨hc₀.lift _ _ w, hc₀.lift_fst _ _ w, hc₀.lift_snd _ _ w, ?_, ?_⟩
  · refine IsPullback.of_right (h₁₂ := h₀) (h₂₂ := Spec.map (CommRingCat.ofHom δ)) ?_ (hc₀.lift_snd _ _ w) hc₀
    rw [hc₀.lift_fst _ _ w, hφδ']
    exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
  · apply hc₀.hom_ext
    · rw [Category.assoc, hc₀.lift_fst _ _ w, Category.comp_id, hg₀]
    · rw [Category.assoc, hc₀.lift_snd _ _ w, ← Category.assoc, D₀.cart.w, Category.assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, hφ, D₀'.cart.w]

theorem exists_slice {X X' : Scheme.{0}} (h₀ : X' ⟶ X) [IsAffineHom h₀] (k : X ⟶ X') (hk : k ≫ h₀ = 𝟙 _)
    (𝒰 : X.OrderedAffineCover) {n : ℕ} (s : 𝒰.Idx n) :
    ∃ r : (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑((𝒰.comap h₀).inter s), r ≫ ((𝒰.comap h₀).inter s).ι = (𝒰.inter s).ι ≫ k ∧ Mono r := by
  have hrange : Set.range ((𝒰.inter s).ι ≫ k).base ⊆ Set.range ((𝒰.comap h₀).inter s).ι.base := by
    rw [Scheme.Opens.range_ι, Scheme.OrderedAffineCover.comap_inter]
    rintro x ⟨y, rfl⟩
    show h₀.base (((𝒰.inter s).ι ≫ k).base y) ∈ (𝒰.inter s : Set X)
    rw [← Scheme.Hom.comp_apply, Category.assoc, hk, Category.comp_id]
    exact (𝒰.inter s).range_ι.le ⟨y, rfl⟩
  haveI : Mono k := ⟨fun a b hab => by simpa [hk] using congrArg (· ≫ h₀) hab⟩
  refine ⟨IsOpenImmersion.lift _ _ hrange, IsOpenImmersion.lift_fac _ _ hrange, ?_⟩
  exact mono_of_mono_fac (IsOpenImmersion.lift_fac _ _ hrange)

end Sections
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian.P2mTripleRing"

section SelfReglue

variable {B B₁ : Type} [CommRing B] [CommRing B₁] [Algebra B B₁]
  {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}

theorem isRegluingBy_refl (D₀ : BareDeformation f₁ L₁ B) (𝒰 : D₀.A.OrderedAffineCover) :
    D₀.IsRegluingBy 𝒰 (fun s => Iso.refl _) D₀ := by
  refine ⟨fun _ => by simp, fun _ => by simp, fun i => (𝒰.U i).ι, fun i => inferInstance, fun i => rfl, ?_, ?_, ?_⟩
  · intro x
    have hx : x ∈ (⊤ : D₀.A.Opens) := trivial
    rw [← 𝒰.iSup_eq_top, TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  · intro i
    exact morphismRestrict_ι _ _
  · intro s
    simp only [Iso.refl_hom, Category.id_comp, Scheme.homOfLE_ι]

end SelfReglue
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian.P2mTripleRing"

section Bridge

theorem fromSpec_comp_eq {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) := by
  letI := algebraOfHom f U
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of R))) hU
    (show U ≤ f ⁻¹ᵁ ⊤ by simp)
  rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

theorem flat_sections {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [hf : Flat f] {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    Module.Flat R Γ(X, U) := by
  have h := HasRingHomProperty.appLE @Flat f hf ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  have h' : RingHom.Flat ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top).hom := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact h'

theorem isoSpec_inv_comp_comp_isoSpec_hom {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (τ : (↑U : Scheme.{u}) ⟶ ↑U) :
    hU.isoSpec.inv ≫ τ ≫ hU.isoSpec.hom = Spec.map (U.topIso.inv ≫ τ.appTop ≫ U.topIso.hom) := by
  haveI : IsAffine U := hU
  simp only [IsAffineOpen.isoSpec, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom, Iso.op_inv,
    Iso.op_hom, Iso.symm_inv, Iso.symm_hom, Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc, Spec.map_comp]
  rw [← Scheme.isoSpec_inv_naturality_assoc, Iso.inv_hom_id_assoc]

theorem exists_algHom_of_over {B : Type u} [CommRing B] {X : Scheme.{u}} (f : X ⟶ Spec (.of B)) {U : X.Opens}
    (hU : IsAffineOpen U) (τ : (↑U : Scheme.{u}) ⟶ ↑U) (hτ : τ ≫ U.ι ≫ f = U.ι ≫ f) :
    letI := algebraOfHom f U
    ∃ ψ : Γ(X, U) →ₐ[B] Γ(X, U), ψ.toRingHom = (U.topIso.inv ≫ τ.appTop ≫ U.topIso.hom).hom ∧
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hU.fromSpec = hU.isoSpec.inv ≫ τ ≫ U.ι := by
  letI := algebraOfHom f U
  have key : Spec.map (U.topIso.inv ≫ τ.appTop ≫ U.topIso.hom) ≫ hU.fromSpec = hU.isoSpec.inv ≫ τ ≫ U.ι := by
    rw [← isoSpec_inv_comp_comp_isoSpec_hom, Category.assoc, Category.assoc, ← IsAffineOpen.isoSpec_inv_ι, Iso.hom_inv_id_assoc]
  have hover : Spec.map (U.topIso.inv ≫ τ.appTop ≫ U.topIso.hom) ≫ Spec.map (CommRingCat.ofHom (algebraMap B Γ(X, U))) =
      Spec.map (CommRingCat.ofHom (algebraMap B Γ(X, U))) := by
    rw [← fromSpec_comp_eq f hU, ← Category.assoc, key, Category.assoc, Category.assoc, hτ, ← Category.assoc,
      IsAffineOpen.isoSpec_inv_ι]
  have hcomm : CommRingCat.ofHom (algebraMap B Γ(X, U)) ≫ (U.topIso.inv ≫ τ.appTop ≫ U.topIso.hom) =
      CommRingCat.ofHom (algebraMap B Γ(X, U)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hover]
  refine ⟨{ toRingHom := (U.topIso.inv ≫ τ.appTop ≫ U.topIso.hom).hom, commutes' := fun b => ?_ }, rfl, ?_⟩
  · have := congrArg (fun φ : CommRingCat.of B ⟶ Γ(X, U) => φ.hom b) hcomm
    simpa using this
  · show Spec.map (CommRingCat.ofHom (U.topIso.inv ≫ τ.appTop ≫ U.topIso.hom).hom) ≫ hU.fromSpec = _
    rw [CommRingCat.ofHom_hom, key]

end Bridge
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian.P2mTripleRing"

end GoodReductionJacobian.P2mKSComb
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian.P2mTripleRing"
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian.P2mTripleRing"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw.FormalCoordinates RelativeGroupLaw AbelianSchemePropertyBundle BareDeformation RelativeGroupLaw.baseChange BareDeformation.exists_isRegluingBy_of_isRegluingBy_of_isPullback BareDeformation.exists_overlap_isos_comap_of_sections BareDeformation.exists_cocycle_of_isRegluingBy BareDeformation.appTop_eq_add_mul_sub_of_slices BareDeformation.exists_isPullback_isFormalCoordinates_map_of_ringHom_comp_eq BareDeformation.exists_glued_scheme_of_overlap_isos BareDeformation.exists_relativeGroupLaw_of_isPullback_of_smooth BareDeformation.exists_deformation_isFormalCoordinates_liftsCoordinates BareDeformation.isIso_of_isRegluingBy_of_forall_comp_hom_eq BareDeformation.exists_iso_one_comp_eq_mapPt_mul_of_isIso BareDeformation.isFormalCoordinates_and_liftsCoordinates_mapPt_inv BareDeformation.isIso_of_isFormalCoordinates_of_liftsCoordinates BareDeformation.isShiftBy_of_isShiftBy_of_isRegluingBy_of_exists_d_eq_sub"
namespace P2mKSComb
p2m_open "GoodReductionJacobian"

section SameTau

theorem deformationIsIso_of_isRegluingBy_of_isRegluingBy
    (B B₁ : Type) [CommRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (Ĝ₁ : MvFormalGroup 2 B₁) (θ₁ : RelativeGroupLaw.FormalCoordinates f₁ 2) (hθ₁ : L₁.IsFormalCoordinates Ĝ₁ θ₁)
    (D₀ D D' : BareDeformation f₁ L₁ B) (𝒰 : D₀.A.OrderedAffineCover)
    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (hD : D₀.IsRegluingBy 𝒰 τ D) (hD' : D₀.IsRegluingBy 𝒰 τ D')
    (G G' : MvFormalGroup.Deformation Ĝ₁ B)
    (θ : RelativeGroupLaw.FormalCoordinates D.f 2) (θ' : RelativeGroupLaw.FormalCoordinates D'.f 2)
    (hθ : D.L.IsFormalCoordinates G.F θ) (hθ' : D'.L.IsFormalCoordinates G'.F θ')
    (hl : D.LiftsCoordinates θ₁ θ) (hl' : D'.LiftsCoordinates θ₁ θ') :
    G.IsIso G' := by
  have hDD' : D.IsIso D' :=
    BareDeformation.isIso_of_isRegluingBy_of_forall_comp_hom_eq hπ hker D₀ D D' 𝒰 τ τ hD hD' (fun _ => Iso.refl _)
      (fun i => by simp) (fun i => by simp) (fun _ _ => Iso.refl _) (fun s j => by simp) (fun s => by simp)
  have hup := BareDeformation.exists_iso_one_comp_eq_mapPt_mul_of_isIso B B₁ D D' hDD'
  obtain ⟨e, he, hge, -, hmul⟩ := hup
  have htr := BareDeformation.isFormalCoordinates_and_liftsCoordinates_mapPt_inv B B₁ θ₁ D D' e he hge hmul G'.F θ' hθ' hl'
  obtain ⟨hθ'', hl''⟩ := htr
  have huniq := BareDeformation.isIso_of_isFormalCoordinates_of_liftsCoordinates B B₁ hπ hker Ĝ₁ θ₁ hθ₁ D G G' θ _ hθ hθ'' hl hl''
  obtain ⟨φ, hφinv, hφX, -⟩ := huniq
  exact ⟨φ, hφinv, hφX⟩

end SameTau
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian.P2mTripleRing"

section Main

open GoodReductionJacobian.P2mTripleRing GoodReductionJacobian.P2mKSComb

set_option maxHeartbeats 6400000 in

theorem _root_.P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.solution
    {q : ℕ} [Fact q.Prime]
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [IsAlgClosed (ResidueField B)]
    [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    (hsmall : RingHom.ker (algebraMap B B₁) * maximalIdeal B = ⊥)
    (hq : IsNilpotent ((q : ℕ) : B))
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁) (hc₁ : L₁.IsCommutative)
    (h₁ : AbelianSchemePropertyBundle B₁ f₁)
    (F : MvFormalGroup 2 B) [F.IsComm]
    (θ₁ : RelativeGroupLaw.FormalCoordinates f₁ 2) (hθ₁ : L₁.IsFormalCoordinates (F.map (algebraMap B B₁)) θ₁)
    (hinf₁ : ∀ (C : Type) [CommRing C] [Algebra B₁ C] (m : ℕ) (P : SchemeHomOver (Scheme.specOver (𝒪 := B₁) C) f₁),
      nsmulPt L₁ (Scheme.specOver (𝒪 := B₁) C) (q ^ m) P = L₁.one (Scheme.specOver (𝒪 := B₁) C) →
        ∃ J : Ideal C, IsNilpotent J ∧ L₁.IsInfinitesimal J P)
    (hheight : ∀ (k : Type) [Field k] (ρ : B →+* k), Function.Surjective ρ →
      Module.finrank k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range ((F.map ρ).nthSeries q))) = q ^ 4)
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    [Module (ResidueField B)ᵐᵒᵖ V] [IsCentralScalar (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))

    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f]
    (𝒰 : D₀.A.OrderedAffineCover) (i₀ : 𝒰.ι) (e₀ : Spec (CommRingCat.of B) ⟶ ↑(𝒰.U i₀)) (he₀ : e₀ ≫ (𝒰.U i₀).ι = (D₀.L.one (𝟙 _)).1)

    (e₁ : Spec (CommRingCat.of (ResidueField B)) ⟶ (((𝒰.baseChange D₀.f (ResidueField B)).U i₀) : Scheme.{0}))
    (he₁ : e₁ ≫ ((𝒰.baseChange D₀.f (ResidueField B)).U i₀).ι = ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).one (𝟙 _)).1)
    (σ : ∀ s : 𝒰.Idx 1,
      letI := algebraOfHom D₀.f (𝒰.inter s)
      ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s)) ≃+* Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s))
    (hσ₁ : ∀ (s : 𝒰.Idx 1) (x : Γ(D₀.A, 𝒰.inter s)),
      letI := algebraOfHom D₀.f (𝒰.inter s)
      σ s ((1 : (ResidueField B)) ⊗ₜ[B] x) =
        ((pullback D₀.f (specMap B (ResidueField B))).presheaf.map (homOfLE (𝒰.baseChange_inter_le D₀.f (ResidueField B) s)).op).hom
          (((pullback.fst D₀.f (specMap B (ResidueField B))).app (𝒰.inter s)).hom x))
    (hσ₂ : ∀ (s : 𝒰.Idx 1) (a : (ResidueField B)),
      letI := algebraOfHom D₀.f (𝒰.inter s)
      letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).inter s)
      σ s (a ⊗ₜ[B] (1 : Γ(D₀.A, 𝒰.inter s))) = algebraMap (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s) a)
    (G₀ : MvFormalGroup.Deformation (F.map (algebraMap B B₁)) B) [G₀.F.IsComm]
    (θ₀ : RelativeGroupLaw.FormalCoordinates D₀.f 2) (hθ₀ : D₀.L.IsFormalCoordinates G₀.F θ₀) (hl₀ : D₀.LiftsCoordinates θ₁ θ₀)

    (r : ResidueField B)
    (c : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) (((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom
          (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)))
    (hc : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ
        ∈ LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))
    (c' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) (((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom
          (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)))
    (hc' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      (c' : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ
        ∈ LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))
    (τ τ' τ'' : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D D' D'' : BareDeformation f₁ L₁ B)
    (hD : D₀.IsRegluingBy 𝒰 τ D) (hD' : D₀.IsRegluingBy 𝒰 τ' D') (hD'' : D₀.IsRegluingBy 𝒰 τ'' D'')
    (hτ : ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ (𝒰.inter s).ι)
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
            σ s (cs a ξ) = (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ s)
    (hτ' : ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ' s).hom ≫ (𝒰.inter s).ι)
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
            σ s (cs a ξ) = (c' : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ s)
    (hτ'' : ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ'' s).hom ≫ (𝒰.inter s).ι)
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
            σ s (cs a ξ) = ((c + r • c') : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ s)

    (G : MvFormalGroup.Deformation (F.map (algebraMap B B₁)) B) [G.F.IsComm]
    (θ : RelativeGroupLaw.FormalCoordinates D.f 2) (hθ : D.L.IsFormalCoordinates G.F θ) (hl : D.LiftsCoordinates θ₁ θ)
    (G' : MvFormalGroup.Deformation (F.map (algebraMap B B₁)) B) [G'.F.IsComm]
    (θ' : RelativeGroupLaw.FormalCoordinates D'.f 2) (hθ' : D'.L.IsFormalCoordinates G'.F θ') (hl' : D'.LiftsCoordinates θ₁ θ')
    (G'' : MvFormalGroup.Deformation (F.map (algebraMap B B₁)) B) [G''.F.IsComm]
    (θ'' : RelativeGroupLaw.FormalCoordinates D''.f 2) (hθ'' : D''.L.IsFormalCoordinates G''.F θ'') (hl'' : D''.LiftsCoordinates θ₁ θ'')
    (w w' : Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] MvFormalGroup.firstOrderDeformationSpace (F.map (IsLocalRing.residue B)))
    (h : MvFormalGroup.Deformation.IsShiftBy V ι F w G₀ G) (h' : MvFormalGroup.Deformation.IsShiftBy V ι F w' G₀ G') :
    MvFormalGroup.Deformation.IsShiftBy V ι F (w + r • w') G₀ G'' := by
  classical

  have hJJ : ∀ j j' : B, j ∈ RingHom.ker (algebraMap B B₁) → j' ∈ RingHom.ker (algebraMap B B₁) → j * j' = 0 := by
    intro j j' hj hj'
    have := Ideal.mul_mem_mul hj (hI hj')
    rwa [hsmall, Ideal.mem_bot] at this
  obtain ⟨al, hal⟩ := IsLocalRing.residue_surjective r
  have hUaff : ∀ s : 𝒰.Idx 1, IsAffineOpen (𝒰.inter s) := fun s => Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s

  haveI hTloc : IsLocalRing (T B B₁) := isLocalRing B B₁ hker
  haveI hTart : IsArtinianRing (T B B₁) := isArtinianRing B B₁
  haveI hTac : IsAlgClosed (ResidueField (T B B₁)) := isAlgClosed_residueField B B₁ hker
  have hπT : Function.Surjective (algebraMap (T B B₁) B₁) := surjective_algebraMap B B₁ hπ
  have hkerT : IsNilpotent (RingHom.ker (algebraMap (T B B₁) B₁)) := isNilpotent_ker B B₁ hker
  have hsmallT : RingHom.ker (algebraMap (T B B₁) B₁) * maximalIdeal (T B B₁) = ⊥ := ker_mul_maximalIdeal B B₁ hker hI hsmall

  have hbc₀ := BareDeformation.exists_isPullback_isFormalCoordinates_map_of_ringHom_comp_eq B (T B B₁) B₁ (δ B B₁) (comp_δ B B₁)
    (F.map (algebraMap B B₁)) θ₁ D₀ G₀ θ₀ hθ₀ hl₀
  obtain ⟨D₀T, h₀, hc₀, hg₀, -, -⟩ := hbc₀
  haveI : IsAffineHom h₀ := MorphismProperty.of_isPullback (P := @IsAffineHom) hc₀.flip inferInstance
  haveI : IsSeparated D₀T.f := D₀T.bundle.proper.toIsSeparated

  obtain ⟨k₀, hk₀, hk₀f, hk₀c, hk₀g⟩ := exists_section D₀ D₀T (δ B B₁) (p₀ B B₁) (p₀_comp_δ B B₁) (comp_p₀ B B₁) h₀ hc₀ hg₀
  obtain ⟨k₁, hk₁, hk₁f, hk₁c, hk₁g⟩ := exists_section D₀ D₀T (δ B B₁) (p₁ B B₁) (p₁_comp_δ B B₁) (comp_p₁ B B₁) h₀ hc₀ hg₀
  obtain ⟨k₂, hk₂, hk₂f, hk₂c, hk₂g⟩ := exists_section D₀ D₀T (δ B B₁) (p₂ B B₁) (p₂_comp_δ B B₁) (comp_p₂ B B₁) h₀ hc₀ hg₀
  obtain ⟨kα, hkα, hkαf, hkαc, hkαg⟩ := exists_section D₀ D₀T (δ B B₁) (α B B₁ al hJJ) (α_comp_δ B B₁ al hJJ) (comp_α B B₁ al hJJ) h₀ hc₀ hg₀
  have sl₀ := fun s : 𝒰.Idx 1 => exists_slice h₀ k₀ hk₀ 𝒰 s
  have sl₁ := fun s : 𝒰.Idx 1 => exists_slice h₀ k₁ hk₁ 𝒰 s
  have sl₂ := fun s : 𝒰.Idx 1 => exists_slice h₀ k₂ hk₂ 𝒰 s
  have slα := fun s : 𝒰.Idx 1 => exists_slice h₀ kα hkα 𝒰 s
  choose r₀ hr₀ hm₀ using sl₀
  choose r₁ hr₁ hm₁ using sl₁
  choose r₂ hr₂ hm₂ using sl₂
  choose rα hrα hmα using slα

  have hcocτ := BareDeformation.exists_cocycle_of_isRegluingBy B B₁ hπ hker D₀ 𝒰 τ D hD
  have hcocτ' := BareDeformation.exists_cocycle_of_isRegluingBy B B₁ hπ hker D₀ 𝒰 τ' D' hD'

  have hfat := BareDeformation.exists_overlap_isos_comap_of_sections (T B B₁) B B₁ hπ (δ B B₁) (comp_δ B B₁) (p₀ B B₁) (p₁ B B₁) (p₂ B B₁)
    (p₀_comp_δ B B₁) (p₁_comp_δ B B₁) (p₂_comp_δ B B₁) (comp_p₀ B B₁) (comp_p₁ B B₁) (comp_p₂ B B₁)
    (fun x y h0 h1 h2 => ext_of_p B B₁ h0 h1 h2) (fun b₀ b₁ b₂ h1 h2 => exists_of_congr B B₁ b₀ b₁ b₂ h1 h2)
    D₀ D₀T h₀ hc₀ hg₀ k₀ k₁ k₂ hk₀ hk₁ hk₂ hk₀f hk₁f hk₂f 𝒰 τ τ' hD.1 hD.2.1 hD'.1 hD'.2.1 hcocτ hcocτ'
  obtain ⟨σT, hσTB, hσTg, hcocσ, hs₀, hs₁, hs₂⟩ := hfat

  have hrg3 := BareDeformation.exists_glued_scheme_of_overlap_isos (T B B₁) B₁ hπT hkerT f₁ L₁ D₀T (𝒰.comap h₀) σT hσTB hσTg hcocσ
  obtain ⟨X, fX, ιU, gX, hblock, hcartX, hsmX⟩ := hrg3
  have hrg4 := BareDeformation.exists_relativeGroupLaw_of_isPullback_of_smooth (T B B₁) B₁ hπT hkerT hsmallT f₁ L₁ hc₁ h₁ fX hsmX gX hcartX
  obtain ⟨LX, hLXc, hbX, hgXmul⟩ := hrg4
  let P : BareDeformation f₁ L₁ (T B B₁) := ⟨X, fX, LX, hLXc, hbX, gX, hcartX, hgXmul⟩
  have hP : D₀T.IsRegluingBy (𝒰.comap h₀) σT P := ⟨hσTB, hσTg, ιU, hblock⟩

  have hfe := BareDeformation.exists_deformation_isFormalCoordinates_liftsCoordinates (T B B₁) B₁ hπT hkerT
    (F.map (algebraMap B B₁)) θ₁ hθ₁ P
  obtain ⟨GP, θP, hGPc, hθP, hlP⟩ := hfe
  haveI := hGPc

  have hbcq₀ := BareDeformation.exists_isPullback_isFormalCoordinates_map_of_ringHom_comp_eq (T B B₁) B B₁ (p₀ B B₁) (comp_p₀ B B₁)
    (F.map (algebraMap B B₁)) θ₁ P GP θP hθP hlP
  obtain ⟨Dq₀, hq₀, hcq₀, hgq₀, -, Gq₀, θq₀, hGq₀F, hGq₀c, hθq₀, hlq₀, -⟩ := hbcq₀
  have hbcq₁ := BareDeformation.exists_isPullback_isFormalCoordinates_map_of_ringHom_comp_eq (T B B₁) B B₁ (p₁ B B₁) (comp_p₁ B B₁)
    (F.map (algebraMap B B₁)) θ₁ P GP θP hθP hlP
  obtain ⟨Dq₁, hq₁, hcq₁, hgq₁, -, Gq₁, θq₁, hGq₁F, hGq₁c, hθq₁, hlq₁, -⟩ := hbcq₁
  have hbcq₂ := BareDeformation.exists_isPullback_isFormalCoordinates_map_of_ringHom_comp_eq (T B B₁) B B₁ (p₂ B B₁) (comp_p₂ B B₁)
    (F.map (algebraMap B B₁)) θ₁ P GP θP hθP hlP
  obtain ⟨Dq₂, hq₂, hcq₂, hgq₂, -, Gq₂, θq₂, hGq₂F, hGq₂c, hθq₂, hlq₂, -⟩ := hbcq₂
  have hbcqα := BareDeformation.exists_isPullback_isFormalCoordinates_map_of_ringHom_comp_eq (T B B₁) B B₁ (α B B₁ al hJJ)
    (comp_α B B₁ al hJJ) (F.map (algebraMap B B₁)) θ₁ P GP θP hθP hlP
  obtain ⟨Dqα, hqα, hcqα, hgqα, -, Gqα, θqα, hGqαF, hGqαc, hθqα, hlqα, -⟩ := hbcqα
  haveI := hGq₀c hGPc; haveI := hGq₁c hGPc; haveI := hGq₂c hGPc; haveI := hGqαc hGPc

  have hrb₀ := BareDeformation.exists_isRegluingBy_of_isRegluingBy_of_isPullback (T B B₁) B B₁ (p₀ B B₁) (comp_p₀ B B₁) D₀ D₀T h₀ k₀ hk₀ hk₀c hk₀g
    𝒰 r₀ hr₀ σT P hP Dq₀ hq₀ hcq₀ hgq₀
  obtain ⟨τq₀, hDq₀, hτq₀⟩ := hrb₀
  have hrb₁ := BareDeformation.exists_isRegluingBy_of_isRegluingBy_of_isPullback (T B B₁) B B₁ (p₁ B B₁) (comp_p₁ B B₁) D₀ D₀T h₀ k₁ hk₁ hk₁c hk₁g
    𝒰 r₁ hr₁ σT P hP Dq₁ hq₁ hcq₁ hgq₁
  obtain ⟨τq₁, hDq₁, hτq₁⟩ := hrb₁
  have hrb₂ := BareDeformation.exists_isRegluingBy_of_isRegluingBy_of_isPullback (T B B₁) B B₁ (p₂ B B₁) (comp_p₂ B B₁) D₀ D₀T h₀ k₂ hk₂ hk₂c hk₂g
    𝒰 r₂ hr₂ σT P hP Dq₂ hq₂ hcq₂ hgq₂
  obtain ⟨τq₂, hDq₂, hτq₂⟩ := hrb₂
  have hrbα := BareDeformation.exists_isRegluingBy_of_isRegluingBy_of_isPullback (T B B₁) B B₁ (α B B₁ al hJJ) (comp_α B B₁ al hJJ) D₀ D₀T h₀
    kα hkα hkαc hkαg 𝒰 rα hrα σT P hP Dqα hqα hcqα hgqα
  obtain ⟨τqα, hDqα, hτqα⟩ := hrbα

  have hte₀ : τq₀ = fun s => Iso.refl _ := by
    funext s; haveI := hm₀ s
    exact Iso.ext ((cancel_mono (r₀ s)).mp (by rw [hτq₀ s, hs₀ s (r₀ s) (hr₀ s), Iso.refl_hom, Category.id_comp]))
  have hte₁ : τq₁ = τ := by
    funext s; haveI := hm₁ s
    exact Iso.ext ((cancel_mono (r₁ s)).mp (by rw [hτq₁ s, hs₁ s (r₁ s) (hr₁ s)]))
  have hte₂ : τq₂ = τ' := by
    funext s; haveI := hm₂ s
    exact Iso.ext ((cancel_mono (r₂ s)).mp (by rw [hτq₂ s, hs₂ s (r₂ s) (hr₂ s)]))
  rw [hte₀] at hDq₀; rw [hte₁] at hDq₁; rw [hte₂] at hDq₂

  have iso₀ : G₀.IsIso Gq₀ := deformationIsIso_of_isRegluingBy_of_isRegluingBy B B₁ hπ hker (F.map (algebraMap B B₁)) θ₁ hθ₁
    D₀ D₀ Dq₀ 𝒰 (fun s => Iso.refl _) (isRegluingBy_refl D₀ 𝒰) hDq₀ G₀ Gq₀ θ₀ θq₀ hθ₀ hθq₀ hl₀ hlq₀
  have iso₁ : G.IsIso Gq₁ := deformationIsIso_of_isRegluingBy_of_isRegluingBy B B₁ hπ hker (F.map (algebraMap B B₁)) θ₁ hθ₁
    D₀ D Dq₁ 𝒰 τ hD hDq₁ G Gq₁ θ θq₁ hθ hθq₁ hl hlq₁
  have iso₂ : G'.IsIso Gq₂ := deformationIsIso_of_isRegluingBy_of_isRegluingBy B B₁ hπ hker (F.map (algebraMap B B₁)) θ₁ hθ₁
    D₀ D' Dq₂ 𝒰 τ' hD' hDq₂ G' Gq₂ θ' θq₂ hθ' hθq₂ hl' hlq₂

  have hformula : ∀ l : Fin 2, Gqα.F.toPowerSeries l = Gq₁.F.toPowerSeries l + al • (Gq₂.F.toPowerSeries l - Gq₀.F.toPowerSeries l) := by
    intro l
    rw [hGqαF, hGq₁F, hGq₂F, hGq₀F]
    show MvPowerSeries.map (α B B₁ al hJJ) (GP.F.toPowerSeries l) = MvPowerSeries.map (p₁ B B₁) (GP.F.toPowerSeries l) +
      al • (MvPowerSeries.map (p₂ B B₁) (GP.F.toPowerSeries l) - MvPowerSeries.map (p₀ B B₁) (GP.F.toPowerSeries l))
    ext n
    simp only [MvPowerSeries.coeff_map, map_add, map_sub, MvPowerSeries.coeff_smul, α_apply]
  have hsh₁ : MvFormalGroup.Deformation.IsShiftBy V ι F w Gq₀ Gq₁ :=
    MvFormalGroup.Deformation.isShiftBy_of_isIso_of_isIso hI V ι hι hιI F w G₀ G Gq₀ Gq₁ h iso₀ iso₁
  have hsh₂ : MvFormalGroup.Deformation.IsShiftBy V ι F w' Gq₀ Gq₂ :=
    MvFormalGroup.Deformation.isShiftBy_of_isIso_of_isIso hI V ι hι hιI F w' G₀ G' Gq₀ Gq₂ h' iso₀ iso₂
  have hshα : MvFormalGroup.Deformation.IsShiftBy V ι F (w + r • w') Gq₀ Gqα :=
    MvFormalGroup.Deformation.isShiftBy_add_smul_of_toPowerSeries_eq_add_smul_sub V ι F Gq₀ Gq₁ Gq₂ Gqα w w' r al hal hformula hsh₁ hsh₂
  have hshα' : MvFormalGroup.Deformation.IsShiftBy V ι F (w + r • w') G₀ Gqα :=
    MvFormalGroup.Deformation.isShiftBy_of_isIso_of_isIso hI V ι hι hιI F (w + r • w') Gq₀ Gqα G₀ Gqα hshα
      ((MvFormalGroup.Deformation.isIso_equivalence _ B).symm iso₀) ((MvFormalGroup.Deformation.isIso_equivalence _ B).refl Gqα)

  haveI hflat : Flat D₀.f := by haveI := D₀.bundle.smooth; infer_instance
  have hτqα'' : ∀ s : 𝒰.Idx 1,
      letI := algebraOfHom D₀.f (𝒰.inter s)
      letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →
          (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
        AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
          ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
          ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τqα s).hom ≫ (𝒰.inter s).ι)
          (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
          (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
        ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)))
          (ξ : Module.Dual (ResidueField B) V),
          σ s (cs a ξ) = ((c + r • c') : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)]
            (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain
              (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ s := by
    intro s
    letI := algebraOfHom D₀.f (𝒰.inter s)
    haveI : Module.Flat B Γ(D₀.A, 𝒰.inter s) := flat_sections D₀.f (hUaff s)
    obtain ⟨cs, hcs, hcsσ⟩ := hτ s
    obtain ⟨cs', hcs', hcs'σ⟩ := hτ' s

    obtain ⟨ψ, hψr, hψS⟩ := exists_algHom_of_over D₀.f (hUaff s) (τ s).hom (hD.1 s)
    obtain ⟨ψ', hψ'r, hψ'S⟩ := exists_algHom_of_over D₀.f (hUaff s) (τ' s).hom (hD'.1 s)
    obtain ⟨ψα, hψαr, hψαS⟩ := exists_algHom_of_over D₀.f (hUaff s) (τqα s).hom (hDqα.1 s)

    have hcong : ∀ (χ : Γ(D₀.A, 𝒰.inter s) →ₐ[B] Γ(D₀.A, 𝒰.inter s)) (β : (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑(𝒰.inter s)),
        (D₀.g ∣_ 𝒰.inter s) ≫ β = D₀.g ∣_ 𝒰.inter s →
        Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ (hUaff s).fromSpec = (hUaff s).isoSpec.inv ≫ β ≫ (𝒰.inter s).ι →
        ∀ x, Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter s))) (χ x) =
          Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter s))) x := by
      intro χ β hβ hχ
      have hrf := AlgebraicGeometry.specMap_comp_fromSpec_eq_specMap_comp_of_morphismRestrict_comp_eq hπ D₀.f f₁ D₀.g D₀.cart
        (𝒰.inter s) (hUaff s) β hβ
      rw [← hχ, ← Category.assoc, ← Spec.map_comp] at hrf
      have hmono : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter s))))) =
          Spec.map (CommRingCat.ofHom χ.toRingHom ≫ CommRingCat.ofHom (Ideal.Quotient.mk _)) :=
        (cancel_mono (hUaff s).fromSpec).mp hrf
      have heq := Spec.map_injective hmono
      intro x
      have := congrArg (fun φ : CommRingCat.of Γ(D₀.A, 𝒰.inter s) ⟶ CommRingCat.of _ => φ.hom x) heq
      simpa using this.symm
    have hψ := hcong ψ (τ s).hom (hD.2.1 s) hψS
    have hψ' := hcong ψ' (τ' s).hom (hD'.2.1 s) hψ'S

    have hslice := BareDeformation.appTop_eq_add_mul_sub_of_slices (T B B₁) B B₁ (δ B B₁) (p₀ B B₁) (p₁ B B₁) (p₂ B B₁)
      (p₀_comp_δ B B₁) (p₁_comp_δ B B₁) (p₂_comp_δ B B₁) (fun x y h0 h1 h2 => ext_of_p B B₁ h0 h1 h2)
      (fun b₀ b₁ b₂ h1 h2 => exists_of_congr B B₁ b₀ b₁ b₂ h1 h2) al (α B B₁ al hJJ) (α_apply B B₁ al hJJ)
      D₀ D₀T h₀ hc₀ k₀ k₁ k₂ kα hk₀ hk₁ hk₂ hkα hk₀f hk₁f hk₂f hkαf 𝒰 hUaff s (r₀ s) (r₁ s) (r₂ s) (rα s)
      (hr₀ s) (hr₁ s) (hr₂ s) (hrα s) (σT s) (τ s) (τ' s) (τqα s) (hs₀ s _ (hr₀ s)) (hs₁ s _ (hr₁ s)) (hs₂ s _ (hr₂ s)) (hτqα s)
    have hψα : ∀ x, ψα x = ψ x + algebraMap B Γ(D₀.A, 𝒰.inter s) al * (ψ' x - x) := by
      intro x
      have := hslice x
      rw [← hψr, ← hψ'r, ← hψαr] at this
      exact this

    rw [← hψS] at hcs
    rw [← hψ'S] at hcs'
    have hcomb := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add_smul_of_apply_eq_add_mul_sub
      (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI Γ(D₀.A, 𝒰.inter s) D₀.f (hUaff s).fromSpec (fromSpec_comp_eq D₀.f (hUaff s))
      (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
      (pullback.fst D₀.f (specMap B (ResidueField B))) (IsPullback.of_hasPullback _ _)
      ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) ((𝒰.baseChange D₀.f (ResidueField B)).isAffineOpen i₀) e₁ he₁
      r al hal ψ ψ' ψα hψ hψ' hψα cs cs' hcs hcs'
    rw [hψαS] at hcomb
    refine ⟨cs + r • cs', hcomb, fun a ξ => ?_⟩
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).inter s)
    have hsmul : ∀ y : (ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s), σ s (r • y) = r • σ s y := by
      intro y
      rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_mul, hσ₂ s r,
        ← Algebra.smul_def]
    simp only [Pi.add_apply, Pi.smul_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add, hsmul, hcsσ, hcs'σ]
    rfl

  have hc'' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      ((c + r • c') : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)]
        (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain
          (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ
        ∈ LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1) := by
    intro a ξ
    simp only [LinearMap.add_apply, LinearMap.smul_apply]
    exact Submodule.add_mem _ (hc a ξ) (Submodule.smul_mem _ r (hc' a ξ))
  exact BareDeformation.isShiftBy_of_isShiftBy_of_isRegluingBy_of_exists_d_eq_sub B B₁ hπ hker hsmall hq f₁ L₁ hc₁ h₁ F θ₁ hθ₁ hinf₁ hheight
    hI V ι hι hιI D₀ 𝒰 i₀ e₀ he₀ e₁ he₁ σ hσ₁ hσ₂ G₀ θ₀ hθ₀ hl₀ (c + r • c') hc'' (c + r • c') hc'' τqα τ'' Dqα D'' hDqα hD'' hτqα'' hτ''
    (fun a ξ => ⟨0, by rw [map_zero, sub_self]⟩) Gqα θqα hθqα hlqα G'' θ'' hθ'' hl'' (w + r • w') hshα'

end Main
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian.P2mTripleRing"

end GoodReductionJacobian.P2mKSComb
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian.P2mTripleRing"
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul.GoodReductionJacobian.P2mTripleRing"

end S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul (solution)
