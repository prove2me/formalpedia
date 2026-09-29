-- Prove2me | solution 1 for ModularCurve.DRModelPackage.exists_ringEquiv_ratFunc_forall_stalkMap_genericPoint_eq_residueFst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/3ea2d264-055a-5452-88b1-06d65a335fdb

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compInf
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jFun_sub_jQFun_sub
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_exists_ringEquiv_ratFunc_forall_stalkMap_genericPoint_eq_residueFst
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_DRModelPackage_exists_ringEquiv_ratFunc_forall_stalkMap_genericPoint_eq_residueFst.ModularCurve ModularCurve.PlaceSpecialization"

noncomputable section

namespace ResMatchOrdCore

universe u

variable {K : Type u} [Field K] {L : Type} [Field L] [Algebra K L]

def read (M : CurveModel K L) {X : Scheme.{u}} (f : M.C ⟶ X) (y : M.C) (x : X) (hx : x = f.base y) :
    X.presheaf.stalk x →+* L :=
  (M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp
    ((algebraMap (M.C.presheaf.stalk y) M.C.functionField).comp
      ((f.stalkMap y).hom.comp (X.presheaf.stalkCongr (.of_eq hx)).hom.hom))

theorem read_apply (M : CurveModel K L) {X : Scheme.{u}} (f : M.C ⟶ X) (y : M.C) (x : X) (hx : x = f.base y)
    (s : X.presheaf.stalk x) :
    read M f y x hx s = M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk y) M.C.functionField
      ((f.stalkMap y).hom ((X.presheaf.stalkCongr (.of_eq hx)).hom.hom s))) := rfl

theorem algebraMap_stalkMap_stalkCongr {C X : Scheme.{u}} [IsIntegral C] (f : C ⟶ X) (y : C) (x : X) (hx : x = f.base y)
    (s : X.presheaf.stalk x) :
    algebraMap (C.presheaf.stalk y) C.functionField ((f.stalkMap y).hom ((X.presheaf.stalkCongr (.of_eq hx)).hom.hom s)) =
      (f.stalkMap (genericPoint C)).hom
        ((X.presheaf.stalkSpecializes (hx ▸ f.base.hom.map_specializes (genericPoint_specializes y))).hom s) := by
  subst hx

  change (C.presheaf.stalkSpecializes (genericPoint_specializes y)).hom ((f.stalkMap y).hom
    ((X.presheaf.stalkSpecializes (specializes_refl (f.base y))).hom s)) = _
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.stalkSpecializes_stalkMap f _ _ (genericPoint_specializes y),
    ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  rfl

theorem read_eq_stalkMap_genericPoint (M : CurveModel K L) {X : Scheme.{u}} (f : M.C ⟶ X) (y : M.C) (x : X)
    (hx : x = f.base y) (s : X.presheaf.stalk x) :
    read M f y x hx s = M.ffEquiv.symm ((f.stalkMap (genericPoint M.C)).hom
      ((X.presheaf.stalkSpecializes (hx ▸ f.base.hom.map_specializes (genericPoint_specializes y))).hom s)) := by
  rw [read_apply, algebraMap_stalkMap_stalkCongr f y x hx s]

section Branch

variable {C X : Scheme.{u}} [IsIntegral C] (f : C ⟶ X)

def branchEmb : IsLocalRing.ResidueField (X.presheaf.stalk (f.base (genericPoint C))) →+* C.functionField :=
  IsLocalRing.ResidueField.lift (f.stalkMap (genericPoint C)).hom

theorem branchEmb_residue (u : X.presheaf.stalk (f.base (genericPoint C))) :
    branchEmb f (IsLocalRing.residue _ u) = (f.stalkMap (genericPoint C)).hom u :=
  IsLocalRing.ResidueField.lift_residue_apply _ _

theorem branchEmb_injective : Function.Injective (branchEmb f) := (branchEmb f).injective

def toBranchResidue (x : X) (h : f.base (genericPoint C) ⤳ x) :
    X.presheaf.stalk x →+* IsLocalRing.ResidueField (X.presheaf.stalk (f.base (genericPoint C))) :=
  (IsLocalRing.residue _).comp (X.presheaf.stalkSpecializes h).hom

theorem toBranchResidue_apply (x : X) (h : f.base (genericPoint C) ⤳ x) (s : X.presheaf.stalk x) :
    toBranchResidue f x h s = IsLocalRing.residue _ ((X.presheaf.stalkSpecializes h).hom s) := rfl

end Branch

theorem read_eq_branchEmb (M : CurveModel K L) {X : Scheme.{u}} (f : M.C ⟶ X) (y : M.C) (x : X) (hx : x = f.base y)
    (s : X.presheaf.stalk x) :
    read M f y x hx s = M.ffEquiv.symm (branchEmb f
      (toBranchResidue f x (hx ▸ f.base.hom.map_specializes (genericPoint_specializes y)) s)) := by
  rw [read_eq_stalkMap_genericPoint, toBranchResidue_apply, branchEmb_residue]

omit [Algebra K L] in
theorem stalkCongr_of_eq_rfl_apply {X : Scheme.{u}} (x : X) (t : X.presheaf.stalk x) :
    (X.presheaf.stalkCongr (.of_eq (rfl : x = x))).hom.hom t = t := by
  show (X.presheaf.stalkSpecializes (specializes_refl x)).hom t = t
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

theorem ord_read_pos (M : CurveModel K L) {X : Scheme.{u}} (f : M.C ⟶ X) (y : M.C) (hy : IsClosed ({y} : Set M.C)) (x : X)
    (hx : x = f.base y) (t : X.presheaf.stalk x) (ht : t ∈ IsLocalRing.maximalIdeal _) (h0 : read M f y x hx t ≠ 0) :
    0 < (M.placeOfPoint ⟨y, hy⟩).ord (read M f y x hx t) := by
  subst hx

  set u : M.C.presheaf.stalk y := (f.stalkMap y).hom ((X.presheaf.stalkCongr (.of_eq rfl)).hom.hom t) with hu_def
  have hu : u ∈ IsLocalRing.maximalIdeal (M.C.presheaf.stalk y) := by
    rw [hu_def, stalkCongr_of_eq_rfl_apply]
    exact map_nonunit (f.stalkMap y).hom t ht

  let a : M.C.presheaf.stalk y →+* L :=
    (M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp (algebraMap (M.C.presheaf.stalk y) M.C.functionField)
  have ha : ∀ z, a z = M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk y) M.C.functionField z) := fun z => rfl
  have hinj : Function.Injective a :=
    M.ffEquiv.symm.injective.comp (IsFractionRing.injective (M.C.presheaf.stalk y) M.C.functionField)
  have hrange : a.range = (M.placeOfPoint ⟨y, hy⟩).toValuationSubring.toSubring := M.range_stalk_eq ⟨y, hy⟩
  have hmem : ∀ z, a z ∈ (M.placeOfPoint ⟨y, hy⟩).toValuationSubring := fun z => by
    have h : a z ∈ a.range := ⟨z, rfl⟩
    rw [hrange] at h
    exact h
  have hread : read M f y (f.base y) rfl t = a u := rfl
  rw [hread] at h0 ⊢
  refine ((M.placeOfPoint ⟨y, hy⟩).mem_maximalIdeal_iff_ord_pos h0 (hmem u)).mp ?_

  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  obtain ⟨w', hw'⟩ := hunit.exists_right_inv
  obtain ⟨z, hz⟩ : ((w' : (M.placeOfPoint ⟨y, hy⟩).toValuationSubring) : L) ∈ a.range := by
    rw [hrange]; exact w'.2
  have h1 : a (u * z) = a 1 := by
    rw [map_mul, map_one, hz]
    exact congrArg Subtype.val hw'
  have h2 : u * z = 1 := hinj h1
  exact (IsLocalRing.mem_maximalIdeal _ |>.mp hu) (IsUnit.of_mul_eq_one z h2)

variable {L' : Type} [Field L'] [Algebra K L']

theorem ord_res_eq_ord_read {S : Type*} [CommRing S] (res : S →+* L') (read : S →+* L) (θ : L ≃+* L')
    (hθ : ∀ s, res s = θ (read s)) (w : Place K L') (P : Place K L) (hpin : ∀ g : L, w.ord (θ g) = P.ord g) (s : S) :
    w.ord (res s) = P.ord (read s) := by
  rw [hθ, hpin]

theorem ord_eq_of_restrict_eq {F S : Type*} [Field F] [CommRing S] (π : S →+* F) (e : F →+* L) (ψ : F →+* L')
    (res : S →+* L') (read : S →+* L) (hres : ∀ s, res s = ψ (π s)) (hread : ∀ s, read s = e (π s))
    (w : Place K L') (P : Place K L) (hpin : ∀ u : F, w.ord (ψ u) = P.ord (e u)) (s : S) :
    w.ord (res s) = P.ord (read s) := by
  rw [hres, hread, hpin]

end ResMatchOrdCore

namespace DescThetaAlgebra

open Function

variable {D L L' : Type*} [CommRing D] [Field L] [Field L']

def GeneratesAsFractions (Θ : D →+* L) : Prop :=
  ∀ z : L, ∃ a b : D, Θ b ≠ 0 ∧ z = Θ a / Θ b

theorem exists_ringEquiv_comp_eq [IsDomain D] (Θ : D →+* L) (Ψ : D →+* L')
    (hΘ : Injective Θ) (hΨ : Injective Ψ) (hΘf : GeneratesAsFractions Θ) (hΨf : GeneratesAsFractions Ψ) :
    ∃ θ : L ≃+* L', ∀ d : D, θ (Θ d) = Ψ d := by

  let F := FractionRing D
  have hΘ0 : nonZeroDivisors D ≤ (nonZeroDivisors L).comap Θ := fun d hd => by
    simpa using (map_ne_zero_iff Θ hΘ).mpr (nonZeroDivisors.ne_zero hd)
  have hΨ0 : nonZeroDivisors D ≤ (nonZeroDivisors L').comap Ψ := fun d hd => by
    simpa using (map_ne_zero_iff Ψ hΨ).mpr (nonZeroDivisors.ne_zero hd)
  let iΘ : F →+* L := IsLocalization.lift (M := nonZeroDivisors D) (g := Θ)
    (fun d => isUnit_iff_ne_zero.mpr ((map_ne_zero_iff Θ hΘ).mpr (nonZeroDivisors.ne_zero d.2)))
  let iΨ : F →+* L' := IsLocalization.lift (M := nonZeroDivisors D) (g := Ψ)
    (fun d => isUnit_iff_ne_zero.mpr ((map_ne_zero_iff Ψ hΨ).mpr (nonZeroDivisors.ne_zero d.2)))
  have hiΘ : ∀ d, iΘ (algebraMap D F d) = Θ d := fun d => IsLocalization.lift_eq _ d
  have hiΨ : ∀ d, iΨ (algebraMap D F d) = Ψ d := fun d => IsLocalization.lift_eq _ d

  have sΘ : Surjective iΘ := fun z => by
    obtain ⟨a, b, hb, rfl⟩ := hΘf z
    refine ⟨algebraMap D F a / algebraMap D F b, ?_⟩
    rw [map_div₀, hiΘ, hiΘ]
  have sΨ : Surjective iΨ := fun z => by
    obtain ⟨a, b, hb, rfl⟩ := hΨf z
    refine ⟨algebraMap D F a / algebraMap D F b, ?_⟩
    rw [map_div₀, hiΨ, hiΨ]
  let eΘ : F ≃+* L := RingEquiv.ofBijective iΘ ⟨iΘ.injective, sΘ⟩
  let eΨ : F ≃+* L' := RingEquiv.ofBijective iΨ ⟨iΨ.injective, sΨ⟩
  refine ⟨eΘ.symm.trans eΨ, fun d => ?_⟩
  have h1 : eΘ (algebraMap D F d) = Θ d := hiΘ d
  rw [RingEquiv.trans_apply, ← h1, RingEquiv.symm_apply_apply]
  exact hiΨ d

theorem ringEquiv_unique (Θ : D →+* L) (Ψ : D →+* L') (hΘf : GeneratesAsFractions Θ)
    (θ θ' : L ≃+* L') (h : ∀ d, θ (Θ d) = Ψ d) (h' : ∀ d, θ' (Θ d) = Ψ d) : θ = θ' := by
  refine RingEquiv.ext fun z => ?_
  obtain ⟨a, b, hb, rfl⟩ := hΘf z
  rw [map_div₀, map_div₀, h, h, h', h']

theorem generatesAsFractions_of_closure_range_eq_top (Θ : D →+* L) (h : Subfield.closure (Set.range Θ) = ⊤) :
    GeneratesAsFractions Θ := by
  intro z
  have hz : z ∈ Subfield.closure (Set.range Θ) := by rw [h]; exact Subfield.mem_top z
  rw [Subfield.mem_closure_iff] at hz
  obtain ⟨y, hy, w, hw, rfl⟩ := hz
  have hcl : Subring.closure (Set.range Θ) = Θ.range := by rw [← RingHom.coe_range]; exact Subring.closure_eq _
  rw [hcl] at hy hw
  obtain ⟨a, rfl⟩ := RingHom.mem_range.mp hy
  obtain ⟨b, rfl⟩ := RingHom.mem_range.mp hw
  by_cases hb : Θ b = 0
  · exact ⟨0, 1, by rw [map_one]; exact one_ne_zero, by rw [hb, div_zero, map_zero, map_one, zero_div]⟩
  · exact ⟨a, b, hb, rfl⟩

theorem generatesAsFractions_modularFunctionFieldC_one (k : Type*) [Field k] (Ψ : D →+* ↥(modularFunctionFieldC k 1))
    (hk : ∀ a : k, algebraMap k ↥(modularFunctionFieldC k 1) a ∈ Set.range Ψ) (hj : jGeomGen k 1 ∈ Set.range Ψ) :
    GeneratesAsFractions Ψ := by
  apply generatesAsFractions_of_closure_range_eq_top

  set T := Subfield.closure (Set.range Ψ) with hT
  rw [eq_top_iff]
  intro x _

  let T' : IntermediateField k (LaurentSeries k) :=
    { (T.map (modularFunctionFieldC k 1).val.toRingHom) with
      algebraMap_mem' := fun a => ⟨algebraMap k _ a, Subfield.subset_closure (hk a), rfl⟩ }
  have hT' : ∀ y : LaurentSeries k, y ∈ T' ↔ ∃ t ∈ T, (t : LaurentSeries k) = y := fun y => Iff.rfl
  have hjT' : jqModC k ∈ T' := (hT' _).mpr ⟨jGeomGen k 1, Subfield.subset_closure hj, rfl⟩
  have hle : modularFunctionFieldC k 1 ≤ T' := by
    rw [modularFunctionFieldC_one, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact hjT'
  obtain ⟨t, ht, htx⟩ := (hT' x).mp (hle x.2)
  rwa [Subtype.ext htx] at ht

end DescThetaAlgebra

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackage.neZero_of_fact_prime DRModel DRModel.toBase DRModelPackage ModularPolynomialData coeffMap_single algebraMap_laurentSeries_eq_single modularFunctionFieldBar PlaceSpecialization.ProlongationTuple.jFun PlaceSpecialization.ProlongationTuple jqModC modularFunctionFieldC modularFunctionFieldC_one PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence jGeomGen transcendental_jqModC modularFunctionFieldFullC DRModel.baseChangeMap DRModelPackage.exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compInf PlaceSpecialization.ProlongationTuple.residue_jFun_sub_jQFun_sub"
namespace DRModelPackage
p2m_export "ModularCurve.DRModelPackage" "neZero_of_fact_prime ratModel compInf w exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compInf"
namespace DescTheta
p2m_open "ModularCurve.DRModelPackage ModularCurve"

attribute [local instance] DRModelPackage.neZero_of_fact_prime

theorem desc_theta₁ (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)
    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) (R : ProlongationTuple P)
    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)
    [IsAlgClosed k] (toκ : O →+* k) (htoκ : ∀ a : O, toκ a = red ⟨ιK (algebraMap O K a), hιA a⟩)
    (hval : ∀ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
        ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
      φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField u) ∈ R.R₁.integers)
    (hj : ∃ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
        ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
      φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField u) =
        ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p)

    (hA : ∀ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
        ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
      u ∈ IsLocalRing.maximalIdeal _ →
        R.residue₁ ⟨φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField u),
          hval u⟩ = 0)

    (hresj : ∀ h, R.residue₁ ⟨ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p, h⟩ = jGeomGen k 1)

    (hDab : ∀ ψ : IsLocalRing.ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
          ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C))) →+* ↥(modularFunctionFieldC k 1),
        (∀ u, ψ (IsLocalRing.residue _ u) =
          R.residue₁ ⟨φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField u),
            hval u⟩) →
        (∃ v, ψ v ∉ Set.range (algebraMap k ↥(modularFunctionFieldC k 1))) →
      ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D)
        (ιk : k →+* D)
        (ικ : IsLocalRing.ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
          ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C))) →+* D)
        (Θ : D →+* (𝔛.ratModel k).C.functionField) (Ψ : D →+* ↥(modularFunctionFieldC k 1)),
        (∀ a : k, Θ (ιk a) = AlgebraicCurve.baseToFunctionField (𝔛.ratModel k).toBase a) ∧
        (∀ v, Θ (ικ v) = IsLocalRing.ResidueField.lift
          (((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).stalkMap (genericPoint ↥(𝔛.ratModel k).C)).hom) v) ∧
        (∀ a : k, Ψ (ιk a) = algebraMap k ↥(modularFunctionFieldC k 1) a) ∧
        (∀ v, Ψ (ικ v) = ψ v) ∧
        Function.Injective Θ ∧
        (∀ z : (𝔛.ratModel k).C.functionField, ∃ a b : D, Θ b ≠ 0 ∧ z = Θ a / Θ b) ∧
        Function.Injective Ψ) :
    ∃ θ : RatFunc k ≃+* ↥(modularFunctionFieldC k 1),
      (∀ a : k, θ (algebraMap k (RatFunc k) a) = algebraMap k ↥(modularFunctionFieldC k 1) a) ∧
      ∀ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
          ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
        θ ((𝔛.ratModel k).ffEquiv.symm
            (((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).stalkMap (genericPoint ↥(𝔛.ratModel k).C)).hom u)) =
          (R.residue₁ ⟨φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField u),
            hval u⟩ : ↥(modularFunctionFieldC k 1)) := by

  let ψ₀ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
      ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)) →+* ↥(modularFunctionFieldC k 1) :=
    R.residue₁.comp ((φ.comp (algebraMap _ _)).codRestrict R.R₁.integers hval)
  have hψ₀ : ∀ u, ψ₀ u = R.residue₁ ⟨φ (algebraMap _ _ u), hval u⟩ := fun u => rfl
  haveI : IsLocalHom ψ₀ := ⟨fun u hu => by
    by_contra h
    exact hu.ne_zero ((hψ₀ u).trans (hA u ((IsLocalRing.mem_maximalIdeal _).mpr h)))⟩
  have hψ : ∀ u, IsLocalRing.ResidueField.lift ψ₀ (IsLocalRing.residue _ u) = R.residue₁ ⟨φ (algebraMap _ _ u), hval u⟩ :=
    fun u => by rw [IsLocalRing.ResidueField.lift_residue_apply]; exact hψ₀ u

  have hψt : ∃ v, IsLocalRing.ResidueField.lift ψ₀ v ∉ Set.range (algebraMap k ↥(modularFunctionFieldC k 1)) := by
    obtain ⟨uj, huj⟩ := hj
    refine ⟨IsLocalRing.residue _ uj, ?_⟩
    have hjmem : ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p ∈ R.R₁.integers := huj ▸ hval uj
    rw [hψ, show (⟨φ (algebraMap _ _ uj), hval uj⟩ : ↥R.R₁.integers) =
      ⟨ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p, hjmem⟩ from Subtype.ext huj, hresj]
    rintro ⟨a, ha⟩
    refine transcendental_jqModC k ?_
    have halg : IsAlgebraic k (jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) := ha ▸ isAlgebraic_algebraMap a
    simpa using halg.algHom (modularFunctionFieldC k 1).val
  obtain ⟨D, _, _, ιk, ικ, Θ, Ψ, hΘk, hΘκ, hΨk, hΨκ, hΘinj, hΘfrac, hΨinj⟩ := hDab (IsLocalRing.ResidueField.lift ψ₀) hψ hψt

  have hΨfrac : DescThetaAlgebra.GeneratesAsFractions Ψ := by
    refine DescThetaAlgebra.generatesAsFractions_modularFunctionFieldC_one k Ψ (fun a => ⟨ιk a, hΨk a⟩) ?_
    obtain ⟨uj, huj⟩ := hj
    refine ⟨ικ (IsLocalRing.residue _ uj), ?_⟩
    rw [hΨκ, hψ, ← hresj (huj ▸ hval uj)]
    congr 1
    exact Subtype.ext huj
  obtain ⟨θ₀, hθ₀⟩ := DescThetaAlgebra.exists_ringEquiv_comp_eq Θ Ψ hΘinj hΨinj hΘfrac hΨfrac

  refine ⟨(𝔛.ratModel k).ffEquiv.trans θ₀, fun a => ?_, fun u => ?_⟩
  · rw [RingEquiv.trans_apply, (𝔛.ratModel k).ffEquiv_algebraMap, ← hΘk, hθ₀, hΨk]
  · rw [RingEquiv.trans_apply, RingEquiv.apply_symm_apply, ← ResMatchOrdCore.branchEmb_residue,
      show ResMatchOrdCore.branchEmb (𝔛.compInf k ≫ DRModel.baseChangeMap toκ) = IsLocalRing.ResidueField.lift
        (((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).stalkMap (genericPoint ↥(𝔛.ratModel k).C)).hom) from rfl,
      ← hΘκ, hθ₀, hΨκ, hψ]

theorem residue₁_const {p : ℕ} [Fact p.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type} [Field k] [CharP k p] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {P : PlaceSpecialization A p 1 data hKr k red hα hβ} (R : ProlongationTuple P) (a : A)
    (h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers) :
    (R.residue₁ ⟨_, h⟩ : ↥(modularFunctionFieldC k 1)) = algebraMap k ↥(modularFunctionFieldC k 1) (red a) := by
  have h1 := R.R₁.residue_algebraMap a
  apply Subtype.ext
  rw [ProlongationTuple.residue₁_apply, R.ι_coe, h1]
  have e1 : (((algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1)) (IsLocalRing.residue A a) :
      ↥(modularFunctionFieldFullC (ResidueField A) 1)) : LaurentSeries (ResidueField A)) =
      algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A a) := rfl
  have e2 : (((algebraMap k ↥(modularFunctionFieldC k 1)) (red a) : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) =
      algebraMap k (LaurentSeries k) (red a) := rfl
  rw [e1, e2, algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single, R.redBar_residue]

end ModularCurve.DRModelPackage.DescTheta

open ModularCurve.DRModelPackage.DescTheta in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)
    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) (R : ProlongationTuple P)
    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)
    [IsAlgClosed k] (toκ : O →+* k) (htoκ : ∀ a : O, toκ a = red ⟨ιK (algebraMap O K a), hιA a⟩)
    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
          ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C))) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ _ trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)))
    (hval : ∀ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
        ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
      φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField u) ∈ R.R₁.integers)
    (hloc : ∀ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
        ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
      u ∈ IsLocalRing.maximalIdeal _ →
        R.residue₁ ⟨φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField u),
          hval u⟩ = 0)
    (hj : ∃ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
        ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
      φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField u) =
        ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p) :
    ∃ θ : RatFunc k ≃+* ↥(modularFunctionFieldC k 1),
      (∀ a : k, θ (algebraMap k (RatFunc k) a) = algebraMap k ↥(modularFunctionFieldC k 1) a) ∧
      ∀ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
          ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
        θ ((𝔛.ratModel k).ffEquiv.symm
            (((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).stalkMap (genericPoint ↥(𝔛.ratModel k).C)).hom u)) =
          (R.residue₁ ⟨φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField u),
            hval u⟩ : ↥(modularFunctionFieldC k 1)) := by
  have hp1 : ¬ p ∣ 1 := (Fact.out : p.Prime).not_dvd_one

  have hresj : ∀ h, R.residue₁ ⟨ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p, h⟩ = jGeomGen k 1 := by
    intro h
    obtain ⟨h₁, -, -, -, e₁, -, -, -⟩ := ModularCurve.PlaceSpecialization.ProlongationTuple.residue_jFun_sub_jQFun_sub R hp1 0
    have hz : ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((0 : A) : AlgebraicClosure ℚ) =
        ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p := by
      rw [ZeroMemClass.coe_zero, map_zero, sub_zero]
    rw [show (⟨ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p, h⟩ : ↥R.R₁.integers) = ⟨_, h₁⟩ from Subtype.ext hz.symm,
      e₁, map_zero, map_zero, sub_zero]

  refine desc_theta₁ p hp 𝔛 O hϖ K ιK φ P R hιA toκ htoκ hval hj hloc hresj ?_
  intro ψ hψ hψt
  refine ModularCurve.DRModelPackage.exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compInf
    p hp 𝔛 O hϖ toκ ψ (fun a => ?_) hψt

  have hmem : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
      ((⟨ιK (algebraMap O K a), hιA a⟩ : A) : AlgebraicClosure ℚ) ∈ R.R₁.integers := by
    have h0 := hval ((((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤
            ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)) trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a))))
    rwa [hφO a] at h0
  rw [hψ, htoκ a, ← residue₁_const R ⟨ιK (algebraMap O K a), hιA a⟩ hmem]
  congr 1
  exact Subtype.ext (hφO a)

end

end S_ModularCurve_DRModelPackage_exists_ringEquiv_ratFunc_forall_stalkMap_genericPoint_eq_residueFst
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_exists_ringEquiv_ratFunc_forall_stalkMap_genericPoint_eq_residueFst (solution)
