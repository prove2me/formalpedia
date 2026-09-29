-- Prove2me | solution 1 for ModularCurve.DRModelPackage.exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/352c799c-5193-5766-9b1e-f5b879b4dbf6

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Theorems.Thm_AlgHom_injective_of_trdeg_le_one_of_exists_transcendental
import Theorems.Thm_RatFunc_trdeg_eq_one
import Theorems.Thm_ModularCurve_DRModelPackage_preimage_closure_image_range_compInf_eq_of_comp_fst_eq
import Theorems.Thm_ModularCurve_DRModel_not_irreducibleSpace_pullback_toBase_of_charP
import Theorems.Thm_ModularCurve_DRModel_isReduced_pullback_toBase_of_charP
import Theorems.Thm_ModularCurve_DRModelPackage_mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero
import Theorems.Thm_ModularCurve_DRModel_baseChangeMap_apply_notMem_preimage_basicOpen
import Theorems.Thm_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing
import Theorems.Thm_ModularCurve_DRModelPackage_isOpenImmersion_restrict_compZero_compl_range_compInf
import Theorems.Thm_ModularCurve_DRModelPackage_isOpenImmersion_restrict_compInf_compl_range_compZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve
open IsLocalRing
open scoped TensorProduct

section
universe u
open TopologicalSpace
namespace E87FF

variable {C Y : Scheme.{u}} [IsIntegral C] (g : C ⟶ Y) (V : Y.Opens) [IsIntegral (V : Scheme.{u})]
  [IsOpenImmersion ((g ⁻¹ᵁ V).ι ≫ g)] [Nonempty (g ⁻¹ᵁ V : C.Opens)]

private noncomputable def _root_.E87FF.lift : ((g ⁻¹ᵁ V : C.Opens) : Scheme.{u}) ⟶ (V : Scheme.{u}) :=
  IsOpenImmersion.lift V.ι ((g ⁻¹ᵁ V).ι ≫ g) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact x.2)

p2m_export "E87FF" "lift"
omit [IsIntegral C] [IsIntegral (V : Scheme.{u})] [IsOpenImmersion ((g ⁻¹ᵁ V).ι ≫ g)]
  [Nonempty (g ⁻¹ᵁ V : C.Opens)] in
theorem lift_ι : lift g V ≫ V.ι = (g ⁻¹ᵁ V).ι ≫ g := IsOpenImmersion.lift_fac _ _ _

scoped instance : IsOpenImmersion (lift g V) := by
  have : IsOpenImmersion (lift g V ≫ V.ι) := by rw [lift_ι]; infer_instance
  exact IsOpenImmersion.of_comp (lift g V) V.ι

theorem lift_genericPoint :
    (lift g V).base (genericPoint ((g ⁻¹ᵁ V : C.Opens) : Scheme.{u})) = genericPoint (V : Scheme.{u}) :=
  genericPoint_eq_of_isOpenImmersion _

omit [IsIntegral (V : Scheme.{u})] [IsOpenImmersion ((g ⁻¹ᵁ V).ι ≫ g)] in
theorem ι_genericPoint :
    (g ⁻¹ᵁ V).ι.base (genericPoint ((g ⁻¹ᵁ V : C.Opens) : Scheme.{u})) = genericPoint C :=
  genericPoint_eq_of_isOpenImmersion _

theorem ι_genericPoint_eq :
    V.ι.base (genericPoint (V : Scheme.{u})) = g.base (genericPoint C) := by
  rw [← lift_genericPoint g V, ← Scheme.Hom.comp_apply, lift_ι, Scheme.Hom.comp_apply, ι_genericPoint]

noncomputable def Λ : (V : Scheme.{u}).functionField ≅ C.functionField :=
  (V : Scheme.{u}).presheaf.stalkCongr (.of_eq (lift_genericPoint g V).symm) ≪≫
    asIso ((lift g V).stalkMap (genericPoint _)) ≪≫
    (asIso ((g ⁻¹ᵁ V).ι.stalkMap (genericPoint _))).symm ≪≫
    C.presheaf.stalkCongr (.of_eq (ι_genericPoint g V))

omit [IsIntegral C] [IsIntegral (V : Scheme.{u})] [IsOpenImmersion ((g ⁻¹ᵁ V).ι ≫ g)] [Nonempty (g ⁻¹ᵁ V : C.Opens)] in

theorem germ_app_congr {X Z : Scheme.{u}} {f₁ f₂ : X ⟶ Z} (e : f₁ = f₂) (W : Z.Opens) (x : X)
    (h₁ : x ∈ f₁ ⁻¹ᵁ W) (h₂ : x ∈ f₂ ⁻¹ᵁ W) (t : Γ(Z, W)) :
    X.presheaf.germ (f₁ ⁻¹ᵁ W) x h₁ (f₁.app W t) = X.presheaf.germ (f₂ ⁻¹ᵁ W) x h₂ (f₂.app W t) := by
  subst e; rfl

theorem Λ_germ (W : Y.Opens) (t : Γ(Y, W))
    (h₁ : V.ι.base (genericPoint (V : Scheme.{u})) ∈ W) (h₂ : g.base (genericPoint C) ∈ W) :
    (Λ g V).hom ((V : Scheme.{u}).presheaf.germ (V.ι ⁻¹ᵁ W) (genericPoint _) h₁ (V.ι.app W t)) =
      C.presheaf.germ (g ⁻¹ᵁ W) (genericPoint C) h₂ (g.app W t) := by
  have e₁ : (lift g V).base (genericPoint _) = genericPoint (V : Scheme.{u}) := lift_genericPoint g V
  have e₂ : (g ⁻¹ᵁ V).ι.base (genericPoint ((g ⁻¹ᵁ V : C.Opens) : Scheme.{u})) = genericPoint C :=
    ι_genericPoint g V
  have hlift : (lift g V).base (genericPoint _) ∈ V.ι ⁻¹ᵁ W := by
    change V.ι.base ((lift g V).base (genericPoint _)) ∈ W
    rwa [e₁]
  have hι : (g ⁻¹ᵁ V).ι.base (genericPoint ((g ⁻¹ᵁ V : C.Opens) : Scheme.{u})) ∈ g ⁻¹ᵁ W := by
    change g.base ((g ⁻¹ᵁ V).ι.base _) ∈ W
    rwa [e₂]
  simp only [Λ, Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, CommRingCat.comp_apply]

  simp only [TopCat.Presheaf.stalkCongr_hom]
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply]

  rw [Scheme.Hom.germ_stalkMap_apply (lift g V) (V.ι ⁻¹ᵁ W) (genericPoint _) hlift]

  have step3 : ((g ⁻¹ᵁ V : C.Opens) : Scheme.{u}).presheaf.germ ((lift g V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W)) (genericPoint _) hlift
        ((lift g V).app (V.ι ⁻¹ᵁ W) (V.ι.app W t)) =
      ((g ⁻¹ᵁ V).ι.stalkMap (genericPoint _))
        (C.presheaf.germ (g ⁻¹ᵁ W) ((g ⁻¹ᵁ V).ι.base (genericPoint _)) hι (g.app W t)) := by
    rw [Scheme.Hom.germ_stalkMap_apply (g ⁻¹ᵁ V).ι (g ⁻¹ᵁ W) (genericPoint _) hι]
    have := germ_app_congr (lift_ι g V) W (genericPoint ((g ⁻¹ᵁ V : C.Opens) : Scheme.{u})) hlift hι t
    simp [Scheme.Hom.comp_app] at this
    exact this
  rw [step3]

  rw [IsIso.hom_inv_id_apply]

  rw [TopCat.Presheaf.germ_stalkSpecializes_apply]

end E87FF
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.E87FF"
end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.E87FF"

noncomputable section

namespace Dock

theorem baseChangeMap_comp_baseChangeMap (p : ℕ) [Fact p.Prime] {O₁ O₂ O₃ : Type} [CommRing O₁] [CommRing O₂] [CommRing O₃]
    (f : O₁ →+* O₂) (g : O₂ →+* O₃) :
    DRModel.baseChangeMap (p := p) g ≫ DRModel.baseChangeMap f = DRModel.baseChangeMap (g.comp f) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, DRModel.baseChangeMap, pullback.lift_fst, Category.comp_id]
  · simp only [Category.assoc, DRModel.baseChangeMap, pullback.lift_snd, pullback.lift_snd_assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]

theorem baseChangeMap_fst (p : ℕ) [Fact p.Prime] {O κ : Type} [CommRing O] [CommRing κ] (f : O →+* κ) :
    DRModel.baseChangeMap (p := p) f ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp only [DRModel.baseChangeMap, pullback.lift_fst, Category.comp_id]

theorem baseChangeMap_snd (p : ℕ) [Fact p.Prime] {O κ : Type} [CommRing O] [CommRing κ] (f : O →+* κ) :
    DRModel.baseChangeMap (p := p) f ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom f) := by
  simp only [DRModel.baseChangeMap, pullback.lift_snd]

theorem isPullback_baseChangeMap (p : ℕ) [Fact p.Prime] {O κ : Type} [CommRing O] [CommRing κ] (f : O →+* κ) :
    IsPullback (DRModel.baseChangeMap (p := p) f) (pullback.snd _ _) (pullback.snd _ _) (Spec.map (CommRingCat.ofHom f)) := by
  have e2 : Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ O)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext_int _ _
  refine IsPullback.of_right ?_ (baseChangeMap_snd p f) (IsPullback.of_hasPullback _ _)
  rw [baseChangeMap_fst, e2]
  exact IsPullback.of_hasPullback _ _

theorem baseChangeMap_surjective (p : ℕ) [Fact p.Prime] {O κ : Type} [CommRing O] [CommRing κ] (f : O →+* κ)
    (hf : Function.Surjective (Spec.map (CommRingCat.ofHom f)).base) :
    Function.Surjective (DRModel.baseChangeMap (p := p) f).base := by
  haveI : Surjective (Spec.map (CommRingCat.ofHom f)) := ⟨hf⟩
  haveI := MorphismProperty.of_isPullback (P := @Surjective) (isPullback_baseChangeMap p f).flip inferInstance
  exact Surjective.surj (f := DRModel.baseChangeMap (p := p) f)

theorem charP_residueField (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)}) : CharP (ResidueField O) p := by
  have h0 : (residue O) ((p : ℕ) : O) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, hϖ]; exact Ideal.mem_span_singleton_self _
  have : ((p : ℕ) : ResidueField O) = 0 := by rw [← map_natCast (residue O) p]; exact h0
  exact (CharP.charP_iff_prime_eq_zero Fact.out).mpr this

theorem isLocalHom_toκ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)}) (k : Type) [Field k] [CharP k p] (toκ : O →+* k) :
    IsLocalHom toκ := by
  refine ⟨fun o ho => ?_⟩
  by_contra hno
  have hmem : o ∈ maximalIdeal O := by rwa [mem_maximalIdeal, mem_nonunits_iff]
  rw [hϖ, Ideal.mem_span_singleton] at hmem
  obtain ⟨t, rfl⟩ := hmem
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul] at ho
  exact not_isUnit_zero ho

section OpenPiece

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (k₀ : Type) [Field k₀] [CharP k₀ p]
  (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (i : k₀ →+* k)

abbrev bck := DRModel.baseChangeMap (p := p) i

abbrev ζ₂ : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))) := (𝔛.compZero k ≫ bck p k₀ k i).base (genericPoint ↥(𝔛.ratModel k).C)

abbrev ζ₁ : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))) := (𝔛.compInf k ≫ bck p k₀ k i).base (genericPoint ↥(𝔛.ratModel k).C)

theorem spec_map_field_surjective : Function.Surjective (Spec.map (CommRingCat.ofHom i)).base := by
  intro x
  refine ⟨IsLocalRing.closedPoint k, ?_⟩
  exact Subsingleton.elim _ _

theorem range_compInf_eq_closure :
    Set.range (𝔛.compInf k).base = closure {(𝔛.compInf k).base (genericPoint ↥(𝔛.ratModel k).C)} := by
  haveI : IsClosedImmersion (𝔛.compInf k) := 𝔛.compInf_isClosedImmersion k
  have h := (genericPoint_spec ↥(𝔛.ratModel k).C).image (𝔛.compInf k).base.hom.continuous
  rw [Set.image_univ, (𝔛.compInf k).isClosedEmbedding.isClosed_range.closure_eq] at h
  exact h.symm

theorem range_compZero_eq_closure :
    Set.range (𝔛.compZero k).base = closure {(𝔛.compZero k).base (genericPoint ↥(𝔛.ratModel k).C)} := by
  haveI : IsClosedImmersion (𝔛.compZero k) := 𝔛.compZero_isClosedImmersion k
  have h := (genericPoint_spec ↥(𝔛.ratModel k).C).image (𝔛.compZero k).base.hom.continuous
  rw [Set.image_univ, (𝔛.compZero k).isClosedEmbedding.isClosed_range.closure_eq] at h
  exact h.symm

theorem closure_ζ₁_eq : closure {ζ₁ p 𝔛 k₀ k i} = closure ((bck p k₀ k i).base '' Set.range (𝔛.compInf k).base) := by
  have h : IsGenericPoint ((𝔛.compInf k).base (genericPoint ↥(𝔛.ratModel k).C)) (Set.range (𝔛.compInf k).base) := by
    rw [IsGenericPoint, ← range_compInf_eq_closure]
  have h2 := h.image (bck p k₀ k i).base.hom.continuous
  rw [IsGenericPoint] at h2
  rw [← h2]
  rfl

theorem closure_ζ₂_eq : closure {ζ₂ p 𝔛 k₀ k i} = closure ((bck p k₀ k i).base '' Set.range (𝔛.compZero k).base) := by
  have h : IsGenericPoint ((𝔛.compZero k).base (genericPoint ↥(𝔛.ratModel k).C)) (Set.range (𝔛.compZero k).base) := by
    rw [IsGenericPoint, ← range_compZero_eq_closure]
  have h2 := h.image (bck p k₀ k i).base.hom.continuous
  rw [IsGenericPoint] at h2
  rw [← h2]
  rfl

theorem preimage_closure_ζ₁ : (bck p k₀ k i).base ⁻¹' closure {ζ₁ p 𝔛 k₀ k i} = Set.range (𝔛.compInf k).base := by
  rw [closure_ζ₁_eq]
  exact (ModularCurve.DRModelPackage.preimage_closure_image_range_compInf_eq_of_comp_fst_eq p 𝔛 k₀ k
    (bck p k₀ k i) (baseChangeMap_fst p i)).1

theorem preimage_closure_ζ₂ : (bck p k₀ k i).base ⁻¹' closure {ζ₂ p 𝔛 k₀ k i} = Set.range (𝔛.compZero k).base := by
  rw [closure_ζ₂_eq]
  exact (ModularCurve.DRModelPackage.preimage_closure_image_range_compInf_eq_of_comp_fst_eq p 𝔛 k₀ k
    (bck p k₀ k i) (baseChangeMap_fst p i)).2

theorem closure_ζ₁_union_closure_ζ₂ : closure {ζ₁ p 𝔛 k₀ k i} ∪ closure {ζ₂ p 𝔛 k₀ k i} = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨y, rfl⟩ := baseChangeMap_surjective p i (spec_map_field_surjective k₀ k i) x
  rcases 𝔛.comp_jointly_surjective k y with hy | hy
  · left
    rw [← Set.mem_preimage, preimage_closure_ζ₁]; exact hy
  · right
    rw [← Set.mem_preimage, preimage_closure_ζ₂]; exact hy

theorem ζ₂_not_mem_closure_ζ₁ : ζ₂ p 𝔛 k₀ k i ∉ closure {ζ₁ p 𝔛 k₀ k i} := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro h
  have hsub : closure {ζ₂ p 𝔛 k₀ k i} ⊆ closure {ζ₁ p 𝔛 k₀ k i} :=
    closure_minimal (Set.singleton_subset_iff.mpr h) isClosed_closure
  have huniv : closure {ζ₁ p 𝔛 k₀ k i} = Set.univ := by
    rw [← closure_ζ₁_union_closure_ζ₂ p 𝔛 k₀ k i, Set.union_eq_left.mpr hsub]
  apply ModularCurve.DRModel.not_irreducibleSpace_pullback_toBase_of_charP p k₀
  have hirr : IsIrreducible (Set.univ : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀))))) := by
    rw [← huniv]; exact isIrreducible_singleton.closure
  exact { isPreirreducible_univ := hirr.2, toNonempty := hirr.1.to_subtype.elim fun x => ⟨x.1⟩ }

theorem ζ₁_not_mem_closure_ζ₂ : ζ₁ p 𝔛 k₀ k i ∉ closure {ζ₂ p 𝔛 k₀ k i} := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro h
  have hsub : closure {ζ₁ p 𝔛 k₀ k i} ⊆ closure {ζ₂ p 𝔛 k₀ k i} :=
    closure_minimal (Set.singleton_subset_iff.mpr h) isClosed_closure
  have huniv : closure {ζ₂ p 𝔛 k₀ k i} = Set.univ := by
    rw [← closure_ζ₁_union_closure_ζ₂ p 𝔛 k₀ k i, Set.union_eq_right.mpr hsub]
  apply ModularCurve.DRModel.not_irreducibleSpace_pullback_toBase_of_charP p k₀
  have hirr : IsIrreducible (Set.univ : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀))))) := by
    rw [← huniv]; exact isIrreducible_singleton.closure
  exact { isPreirreducible_univ := hirr.2, toNonempty := hirr.1.to_subtype.elim fun x => ⟨x.1⟩ }

def U : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))).Opens :=
  ⟨(closure {ζ₁ p 𝔛 k₀ k i})ᶜ, isClosed_closure.isOpen_compl⟩

theorem mem_U_iff (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀))))) : x ∈ U p 𝔛 k₀ k i ↔ x ∉ closure {ζ₁ p 𝔛 k₀ k i} := Iff.rfl

theorem ζ₂_mem_U : ζ₂ p 𝔛 k₀ k i ∈ U p 𝔛 k₀ k i := ζ₂_not_mem_closure_ζ₁ p 𝔛 k₀ k i

theorem U_subset_closure_ζ₂ : ((U p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))).Opens) : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀))))) ⊆ closure {ζ₂ p 𝔛 k₀ k i} := by
  intro x hx
  have := (Set.eq_univ_iff_forall.mp (closure_ζ₁_union_closure_ζ₂ p 𝔛 k₀ k i)) x
  rcases this with h | h
  · exact absurd h hx
  · exact h

theorem closure_U_eq : closure ((U p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))).Opens) : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀))))) = closure {ζ₂ p 𝔛 k₀ k i} := by
  refine le_antisymm (closure_minimal (U_subset_closure_ζ₂ p 𝔛 k₀ k i) isClosed_closure) ?_
  exact closure_mono (Set.singleton_subset_iff.mpr (ζ₂_mem_U p 𝔛 k₀ k i))

scoped instance irreducibleSpace_U : IrreducibleSpace ↥(U p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))).Opens) := by
  have hirr : IsIrreducible ((U p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))).Opens) : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀))))) :=
    ⟨⟨_, ζ₂_mem_U p 𝔛 k₀ k i⟩,
      (isIrreducible_singleton.closure : IsIrreducible (closure {ζ₂ p 𝔛 k₀ k i})).2.open_subset
        (U p 𝔛 k₀ k i).isOpen (U_subset_closure_ζ₂ p 𝔛 k₀ k i)⟩
  exact Subtype.irreducibleSpace hirr

scoped instance isIntegral_U : IsIntegral (U p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))).Opens) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : IsReduced (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))) := ModularCurve.DRModel.isReduced_pullback_toBase_of_charP p k₀
  haveI : IsReduced (U p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))).Opens) := isReduced_of_isOpenImmersion (U p 𝔛 k₀ k i).ι
  haveI : IrreducibleSpace ↥((U p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))).Opens) : Scheme.{0}) := irreducibleSpace_U p 𝔛 k₀ k i
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem ι_genericPoint_U :
    (U p 𝔛 k₀ k i).ι.base (genericPoint ↥((U p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))).Opens) : Scheme.{0})) = ζ₂ p 𝔛 k₀ k i := by
  have h1 := (genericPoint_spec ↥((U p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))).Opens) : Scheme.{0})).image
    (U p 𝔛 k₀ k i).ι.base.hom.continuous
  rw [Set.image_univ, Scheme.Opens.range_ι, closure_U_eq] at h1
  exact h1.eq isGenericPoint_closure

end OpenPiece
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.E87FF"

section BaseChangeOpen

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (k₀ : Type) [Field k₀] [CharP k₀ p]
  (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (i : k₀ →+* k)

abbrev V : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens := (bck p k₀ k i) ⁻¹ᵁ (U p 𝔛 k₀ k i)

theorem coe_V : ((V p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))) = (Set.range (𝔛.compInf k).base)ᶜ := by
  change (bck p k₀ k i).base ⁻¹' (closure {ζ₁ p 𝔛 k₀ k i})ᶜ = _
  rw [Set.preimage_compl, preimage_closure_ζ₁]

theorem mem_V_iff (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))) : y ∈ V p 𝔛 k₀ k i ↔ y ∉ Set.range (𝔛.compInf k).base := by
  rw [← SetLike.mem_coe, coe_V]; rfl

theorem V_subset_range_compZero : ((V p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))) ⊆ Set.range (𝔛.compZero k).base := by
  intro y hy
  rw [coe_V] at hy
  exact (𝔛.comp_jointly_surjective k y).resolve_left hy

theorem sectionFibre_εzero_mem_V :
    (DRModel.sectionFibre 𝔛.εzero (algebraMap ℤ k)).base (IsLocalRing.closedPoint k) ∈ V p 𝔛 k₀ k i := by
  rw [mem_V_iff]
  intro hI
  have hZ : (DRModel.sectionFibre 𝔛.εzero (algebraMap ℤ k)).base (IsLocalRing.closedPoint k) ∈ Set.range (𝔛.compZero k).base :=
    𝔛.εzero_mem_compZero k ⟨IsLocalRing.closedPoint k, rfl⟩
  have hsm : (DRModel.sectionFibre 𝔛.εzero (algebraMap ℤ k)).base (IsLocalRing.closedPoint k) ∈
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) ⁻¹ᵁ 𝔛.smoothLocus) := by
    change (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base
      ((DRModel.sectionFibre 𝔛.εzero (algebraMap ℤ k)).base (IsLocalRing.closedPoint k)) ∈ (𝔛.smoothLocus : Set (DRModel p))
    rw [← TopCat.comp_app, ← Scheme.Hom.comp_base, DRModel.sectionFibre, pullback.lift_fst, Scheme.Hom.comp_base, TopCat.comp_app]
    exact 𝔛.εzero_mem_smoothLocus ⟨_, rfl⟩
  exact ((ModularCurve.DRModelPackage.mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero p 𝔛 k _).mp hsm)
    ⟨hI, hZ⟩

scoped instance irreducibleSpace_V : IrreducibleSpace ↥(V p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) := by
  have hirr : IsIrreducible ((V p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))) := by
    refine ⟨⟨_, sectionFibre_εzero_mem_V p 𝔛 k₀ k i⟩, ?_⟩
    have hZ : IsIrreducible (Set.range (𝔛.compZero k).base) := by
      rw [range_compZero_eq_closure]; exact isIrreducible_singleton.closure
    exact hZ.2.open_subset (V p 𝔛 k₀ k i).isOpen (V_subset_range_compZero p 𝔛 k₀ k i)
  exact Subtype.irreducibleSpace hirr

scoped instance isIntegral_V : IsIntegral (V p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : IsReduced (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) := ModularCurve.DRModel.isReduced_pullback_toBase_of_charP p k
  haveI : IsReduced (V p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) := isReduced_of_isOpenImmersion (V p 𝔛 k₀ k i).ι
  haveI : IrreducibleSpace ↥((V p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0}) := irreducibleSpace_V p 𝔛 k₀ k i
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem isPullback_V :
    IsPullback ((bck p k₀ k i) ∣_ (U p 𝔛 k₀ k i))
      ((V p 𝔛 k₀ k i).ι ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))
      ((U p 𝔛 k₀ k i).ι ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀))))
      (Spec.map (CommRingCat.ofHom i)) :=
  (isPullback_morphismRestrict (bck p k₀ k i) (U p 𝔛 k₀ k i)).paste_vert (isPullback_baseChangeMap p i)

theorem isIntegral_pullback_U :
    letI : Algebra k₀ k := i.toAlgebra
    IsIntegral ↑(pullback ((U p 𝔛 k₀ k i).ι ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀))))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k)))) := by
  letI : Algebra k₀ k := i.toAlgebra
  let e := (isPullback_V p 𝔛 k₀ k i).isoPullback
  haveI : IsIntegral (V p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) := isIntegral_V p 𝔛 k₀ k i
  haveI : IrreducibleSpace ↥(pullback ((U p 𝔛 k₀ k i).ι ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀))))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k)))) :=
    (Homeomorph.irreducibleSpace_iff (Scheme.homeoOfIso e)).mp inferInstance
  haveI : IsReduced (pullback ((U p 𝔛 k₀ k i).ι ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀))))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k)))) := isReduced_of_isOpenImmersion e.inv
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end BaseChangeOpen
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.E87FF"

section ResidueField

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
  (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (i : ResidueField O →+* k)

abbrev bc₀ := DRModel.baseChangeMap (p := p) (residue O)

scoped instance isClosedImmersion_bc₀ : IsClosedImmersion (bc₀ p O) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (residue O))) :=
    IsClosedImmersion.spec_of_surjective _ (by simpa using IsLocalRing.residue_surjective)
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_baseChangeMap p (residue O)).flip inferInstance

variable [CharP (ResidueField O) p]

abbrev ξ₂ : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) := (bc₀ p O).base (ζ₂ p 𝔛 (ResidueField O) k i)

abbrev σ₁ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₂ p 𝔛 O k i) ⟶
    (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.stalk (ζ₂ p 𝔛 (ResidueField O) k i) :=
  (bc₀ p O).stalkMap (ζ₂ p 𝔛 (ResidueField O) k i)

theorem σ₁_surjective : Function.Surjective (σ₁ p 𝔛 O k i) :=
  (bc₀ p O).stalkMap_surjective _

def ιStalkIso : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.stalk ((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.base (genericPoint ↥((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}))) ≅
    (U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).toScheme.presheaf.stalk (genericPoint ↥((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) :=
  @asIso _ _ _ _ ((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.stalkMap (genericPoint ↥((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})))
    (inferInstanceAs <| IsIso ((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.toLRSHom.stalkMap (genericPoint ↥((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}))))

theorem ιStalkIso_hom : (ιStalkIso p 𝔛 O k i).hom = (U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.stalkMap (genericPoint ↥((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) := rfl

abbrev σ₂ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.stalk (ζ₂ p 𝔛 (ResidueField O) k i) ⟶
    (U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).toScheme.presheaf.stalk (genericPoint ↥((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) :=
  ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.stalkCongr (.of_eq (ι_genericPoint_U p 𝔛 (ResidueField O) k i).symm)).hom ≫
    (ιStalkIso p 𝔛 O k i).hom

scoped instance isIso_σ₂ : IsIso (σ₂ p 𝔛 O k i) := IsIso.comp_isIso

abbrev σ := σ₁ p 𝔛 O k i ≫ σ₂ p 𝔛 O k i

theorem σ_surjective : Function.Surjective (σ p 𝔛 O k i) :=
  (ConcreteCategory.bijective_of_isIso (σ₂ p 𝔛 O k i)).2.comp (σ₁_surjective p 𝔛 O k i)

scoped instance isLocalHom_σ : IsLocalHom (σ p 𝔛 O k i).hom := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hmem : a ∈ maximalIdeal _ := by rwa [mem_maximalIdeal, mem_nonunits_iff]
  have h1 : ((bc₀ p O).stalkMap (ζ₂ p 𝔛 (ResidueField O) k i)).hom a ∈ maximalIdeal _ :=
    map_nonunit ((bc₀ p O).stalkMap (ζ₂ p 𝔛 (ResidueField O) k i)).hom a hmem

  have eS : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.stalk (ζ₂ p 𝔛 (ResidueField O) k i) ≃+* ↥(((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).functionField) := (asIso (σ₂ p 𝔛 O k i)).commRingCatIsoToRingEquiv
  have hSf : IsField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.stalk (ζ₂ p 𝔛 (ResidueField O) k i)) := MulEquiv.isField (Field.toIsField ↥(((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).functionField)) eS.toMulEquiv
  have h1' : ((bc₀ p O).stalkMap (ζ₂ p 𝔛 (ResidueField O) k i)).hom a = 0 := by
    have hnu : ¬ IsUnit (((bc₀ p O).stalkMap (ζ₂ p 𝔛 (ResidueField O) k i)).hom a) := (mem_maximalIdeal _).mp h1
    by_contra hne
    obtain ⟨b, hb⟩ := hSf.mul_inv_cancel hne
    exact hnu (isUnit_iff_exists_inv.mpr ⟨b, hb⟩)
  have : (σ p 𝔛 O k i).hom a = 0 := by
    change (σ₂ p 𝔛 O k i).hom (((bc₀ p O).stalkMap (ζ₂ p 𝔛 (ResidueField O) k i)).hom a) = 0
    rw [h1']
    exact map_zero _
  rw [this] at ha
  exact not_isUnit_zero ha

def α : ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₂ p 𝔛 O k i)) →+*
    ↥(((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).functionField) :=
  ResidueField.lift (σ p 𝔛 O k i).hom

theorem α_residue (v : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₂ p 𝔛 O k i)) :
    α p 𝔛 O k i (residue _ v) = (σ p 𝔛 O k i).hom v :=
  ResidueField.lift_residue_apply _ v

theorem α_bijective : Function.Bijective (α p 𝔛 O k i) := by
  refine ⟨(α p 𝔛 O k i).injective, fun y => ?_⟩
  obtain ⟨v, rfl⟩ := σ_surjective p 𝔛 O k i y
  exact ⟨residue _ v, α_residue p 𝔛 O k i v⟩

abbrev constO (ξ : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) : O →+* (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ :=
  ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ ξ trivial).hom.comp
    (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)

theorem not_isUnit_constO_natCast : ¬ IsUnit (constO p O (ξ₂ p 𝔛 O k i) ((p : ℕ) : O)) := by
  intro hu
  apply ModularCurve.DRModel.baseChangeMap_apply_notMem_preimage_basicOpen p O (ResidueField O) (residue O)
    (ζ₂ p 𝔛 (ResidueField O) k i)
  have h1 : (ξ₂ p 𝔛 O k i) ∈ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).basicOpen
      ((((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ⊤).hom
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ((p : ℕ) : O)))) :=
    ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).mem_basicOpen (U := ⊤) _ (ξ₂ p 𝔛 O k i) trivial).mpr hu
  rw [← Scheme.preimage_basicOpen] at h1
  erw [basicOpen_eq_of_affine] at h1
  exact h1

theorem isLocalHom_constO (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)}) :
    IsLocalHom (constO p O (ξ₂ p 𝔛 O k i)) := by
  refine ⟨fun o ho => ?_⟩
  by_contra hno
  have hmem : o ∈ maximalIdeal O := by rwa [mem_maximalIdeal, mem_nonunits_iff]
  rw [hϖ, Ideal.mem_span_singleton] at hmem
  obtain ⟨t, rfl⟩ := hmem
  rw [map_mul] at ho
  exact not_isUnit_constO_natCast p 𝔛 O k i (isUnit_of_mul_isUnit_left ho)

variable (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)})

def j : ResidueField O →+* ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₂ p 𝔛 O k i)) :=
  @ResidueField.map _ _ _ _ _ _ (constO p O (ξ₂ p 𝔛 O k i)) (isLocalHom_constO p 𝔛 O k i hϖ)

theorem j_residue (o : O) : j p 𝔛 O k i hϖ (residue O o) = residue _ (constO p O (ξ₂ p 𝔛 O k i) o) := by
  haveI := isLocalHom_constO p 𝔛 O k i hϖ
  exact ResidueField.map_residue _ o

theorem α_residue_constO (o : O) :
    α p 𝔛 O k i (residue _ (constO p O (ξ₂ p 𝔛 O k i) o)) =
      AlgebraicCurve.baseToFunctionField ((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ pullback.snd (DRModel.toBase p)
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))) (residue O o) := by
  rw [α_residue]

  change (σ₂ p 𝔛 O k i).hom (((bc₀ p O).stalkMap (ζ₂ p 𝔛 (ResidueField O) k i)).hom
    (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ (ξ₂ p 𝔛 O k i) trivial).hom
      (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)))) = _
  erw [Scheme.Hom.germ_stalkMap_apply (bc₀ p O) ⊤ (ζ₂ p 𝔛 (ResidueField O) k i) trivial]

  have hsq : ((bc₀ p O).app ⊤).hom ((((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
      ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) =
      ((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (ResidueField O))).inv.hom (residue O o)) := by
    have h := congrArg (fun φ => (Scheme.Hom.appTop φ).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o))
      (baseChangeMap_snd p (residue O))
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
    have hnat := congrArg (fun φ => φ.hom o) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (residue O)))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at hnat
    rw [← hnat] at h
    exact h
  erw [hsq]

  change (ιStalkIso p 𝔛 O k i).hom.hom ((((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.stalkCongr
      (.of_eq (ι_genericPoint_U p 𝔛 (ResidueField O) k i).symm)).hom).hom
    (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.germ ⊤ (ζ₂ p 𝔛 (ResidueField O) k i) trivial).hom _)) = _
  rw [TopCat.Presheaf.stalkCongr_hom, ← CommRingCat.comp_apply ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.germ ⊤ _ trivial),
    TopCat.Presheaf.germ_stalkSpecializes]
  rw [ιStalkIso_hom]
  erw [Scheme.Hom.germ_stalkMap_apply (U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⊤ (genericPoint ↥((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) trivial]
  rfl

theorem σ₂_germ (W : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) (hW : ζ₂ p 𝔛 (ResidueField O) k i ∈ W)
    (s : Γ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))), W)) (hW' : (U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.base (genericPoint ↥((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) ∈ W) :
    (σ₂ p 𝔛 O k i).hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.germ W (ζ₂ p 𝔛 (ResidueField O) k i) hW).hom s) =
      (((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).presheaf.germ ((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W) (genericPoint ↥((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) hW').hom (((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.app W).hom s) := by
  change (ιStalkIso p 𝔛 O k i).hom.hom ((((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.stalkCongr
      (.of_eq (ι_genericPoint_U p 𝔛 (ResidueField O) k i).symm)).hom).hom
    (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.germ W (ζ₂ p 𝔛 (ResidueField O) k i) hW).hom s)) = _
  rw [TopCat.Presheaf.stalkCongr_hom, ← CommRingCat.comp_apply ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.germ W _ hW),
    TopCat.Presheaf.germ_stalkSpecializes (hy := hW) (h := (Inseparable.of_eq (ι_genericPoint_U p 𝔛 (ResidueField O) k i).symm).ge)]
  rw [ιStalkIso_hom]
  erw [Scheme.Hom.germ_stalkMap_apply (U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι W (genericPoint ↥((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) hW']

end ResidueField
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.E87FF"

theorem base_genericPoint_eq_of_flat {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    f.base (genericPoint X) = genericPoint Y := by
  have hgen := Flat.generalizingMap f
  have hsp : genericPoint Y ⤳ f.base (genericPoint X) := genericPoint_specializes _
  obtain ⟨x', hx', hfx'⟩ := hgen hsp
  have hx'' : genericPoint X ⤳ x' := genericPoint_specializes _
  have heq : x' = genericPoint X := (hx'.antisymm hx'').eq
  rw [← hfx', heq]

section Assembly

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
  (k : Type) [Field k] [CharP k p] [IsAlgClosed k] [Algebra (ResidueField O) k] [CharP (ResidueField O) p]
  (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)})

scoped instance isIntegral_Uk : IsIntegral (pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) :=
  isIntegral_pullback_U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)

scoped instance flat_π : Flat (pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) := MorphismProperty.pullback_fst _ _ inferInstance

theorem π_genericPoint : (pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).base (genericPoint ↥(pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))) = (genericPoint ↥((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) :=
  base_genericPoint_eq_of_flat _

include hϖ in
set_option maxHeartbeats 6400000 in

theorem core
    [algk : Algebra O k] (halgk : algebraMap O k = (algebraMap (ResidueField O) k).comp (residue O))
    [algK : Algebra O (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₂ p 𝔛 O k (algebraMap (ResidueField O) k))))]
    (halgK : ∀ a : O, algebraMap O (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₂ p 𝔛 O k (algebraMap (ResidueField O) k)))) a = residue _ (constO p O (ξ₂ p 𝔛 O k (algebraMap (ResidueField O) k)) a))
    (Θ : k ⊗[O] (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₂ p 𝔛 O k (algebraMap (ResidueField O) k)))) →+* ↥((𝔛.ratModel k).C.functionField))
    (hΘk : ∀ a : k, Θ (a ⊗ₜ 1) = AlgebraicCurve.baseToFunctionField (𝔛.ratModel k).toBase a)
    (hΘK : ∀ v : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₂ p 𝔛 O k (algebraMap (ResidueField O) k)),
      Θ (1 ⊗ₜ residue _ v) = (((𝔛.compZero k ≫ (bck p (ResidueField O) k (algebraMap (ResidueField O) k) ≫ bc₀ p O)).stalkMap (genericPoint ↥(𝔛.ratModel k).C)).hom v))
    (Λ : ↥((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).functionField) →+* ↥((𝔛.ratModel k).C.functionField))
    (hΛsurj : Function.Surjective Λ)
    (hΛ1 : ∀ a : k, Λ (AlgebraicCurve.baseToFunctionField
        (pullback.snd ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) a) =
        AlgebraicCurve.baseToFunctionField (𝔛.ratModel k).toBase a)
    (hΛ2 : ∀ (W : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) (hW : ζ₂ p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) ∈ W) (s : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.obj (Opposite.op W)))
        [Nonempty (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W : ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).Opens) : Scheme.{0})]
        [Nonempty (((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ⁻¹ᵁ ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W) : ((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).Opens) : Scheme.{0})],
        Λ ((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).germToFunctionField ((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ⁻¹ᵁ ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W)) (((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).app ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W)).hom (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.app W).hom s))) =
          ((𝔛.compZero k ≫ bck p (ResidueField O) k (algebraMap (ResidueField O) k)).stalkMap (genericPoint ↥(𝔛.ratModel k).C)).hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.germ W (ζ₂ p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)) hW).hom s)) :
    Function.Injective Θ ∧ ∀ z : ↥((𝔛.ratModel k).C.functionField), ∃ a b, Θ b ≠ 0 ∧ z = Θ a / Θ b := by

  classical

  letI algKU : Algebra (ResidueField O) ↥(((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).functionField) := (AlgebraicCurve.baseToFunctionField ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))))).toAlgebra
  letI algkUk : Algebra k ↥((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).functionField) :=
    (AlgebraicCurve.baseToFunctionField (pullback.snd ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).toAlgebra

  obtain ⟨Φ, hΦinj, hΦfrac, hΦgerm⟩ :=
    AlgebraicGeometry.exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing k ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))))

  letI algK₀ : Algebra (ResidueField O) (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₂ p 𝔛 O k (algebraMap (ResidueField O) k)))) := (j p 𝔛 O k (algebraMap (ResidueField O) k) hϖ).toAlgebra
  haveI towK : IsScalarTower O (ResidueField O) (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₂ p 𝔛 O k (algebraMap (ResidueField O) k)))) := IsScalarTower.of_algebraMap_eq (fun o => by
    rw [halgK]; exact (j_residue p 𝔛 O k (algebraMap (ResidueField O) k) hϖ o).symm)
  haveI towk : IsScalarTower O (ResidueField O) k := IsScalarTower.of_algebraMap_eq (fun o => by
    rw [halgk]; rfl)

  let αe : (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₂ p 𝔛 O k (algebraMap (ResidueField O) k)))) ≃ₐ[(ResidueField O)] ↥(((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).functionField) :=
    AlgEquiv.ofBijective
      { (α p 𝔛 O k (algebraMap (ResidueField O) k)) with
        commutes' := fun r => by
          obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective r
          change α p 𝔛 O k (algebraMap (ResidueField O) k) (j p 𝔛 O k (algebraMap (ResidueField O) k) hϖ (residue O o)) = algebraMap (ResidueField O) ↥(((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).functionField) (residue O o)
          rw [j_residue, α_residue_constO p 𝔛 O k (algebraMap (ResidueField O) k) o]
          rfl }
      (α_bijective p 𝔛 O k (algebraMap (ResidueField O) k))
  have hαe : ∀ v, αe v = α p 𝔛 O k (algebraMap (ResidueField O) k) v := fun v => rfl

  haveI cs1 : TensorProduct.CompatibleSMul O (ResidueField O) k (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₂ p 𝔛 O k (algebraMap (ResidueField O) k)))) := ⟨fun r a v => by
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective r
    have h1 : (residue O o) • a = o • a := IsScalarTower.algebraMap_smul (ResidueField O) o a
    have h2 : (residue O o) • v = o • v := IsScalarTower.algebraMap_smul (ResidueField O) o v
    rw [h1, h2, TensorProduct.smul_tmul]⟩
  haveI cs2 : TensorProduct.CompatibleSMul (ResidueField O) O k (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₂ p 𝔛 O k (algebraMap (ResidueField O) k)))) := ⟨fun o a v => by
    have h1 : (residue O o) • a = o • a := IsScalarTower.algebraMap_smul (ResidueField O) o a
    have h2 : (residue O o) • v = o • v := IsScalarTower.algebraMap_smul (ResidueField O) o v
    rw [← h1, ← h2, TensorProduct.smul_tmul]⟩
  let B : k ⊗[O] (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₂ p 𝔛 O k (algebraMap (ResidueField O) k)))) ≃ₗ[O] k ⊗[(ResidueField O)] (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₂ p 𝔛 O k (algebraMap (ResidueField O) k)))) := TensorProduct.equivOfCompatibleSMul (ResidueField O) O O k (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₂ p 𝔛 O k (algebraMap (ResidueField O) k))))
  have hB : ∀ a v, B (a ⊗ₜ v) = a ⊗ₜ v := fun a v => rfl
  let M : k ⊗[(ResidueField O)] (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₂ p 𝔛 O k (algebraMap (ResidueField O) k)))) ≃ₐ[(ResidueField O)] k ⊗[(ResidueField O)] ↥(((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).functionField) := Algebra.TensorProduct.congr AlgEquiv.refl αe
  have hM : ∀ a v, M (a ⊗ₜ v) = a ⊗ₜ α p 𝔛 O k (algebraMap (ResidueField O) k) v := fun a v => by
    change Algebra.TensorProduct.map _ _ (a ⊗ₜ v) = _
    rw [Algebra.TensorProduct.map_tmul]
    rfl

  let τ : k ⊗[O] (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₂ p 𝔛 O k (algebraMap (ResidueField O) k)))) → k ⊗[(ResidueField O)] ↥(((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).functionField) := fun x => M (B x)
  have hτ : ∀ a v, τ (a ⊗ₜ v) = a ⊗ₜ α p 𝔛 O k (algebraMap (ResidueField O) k) v := fun a v => by
    change M (B (a ⊗ₜ v)) = _; rw [hB, hM]
  have hτbij : Function.Bijective τ := M.bijective.comp B.bijective
  have hτadd : ∀ x y, τ (x + y) = τ x + τ y := fun x y => by change M (B (x + y)) = _; rw [map_add, map_add]
  have hτzero : τ 0 = 0 := by change M (B 0) = 0; rw [map_zero, map_zero]

  have key1 : ∀ (a : k) (v : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₂ p 𝔛 O k (algebraMap (ResidueField O) k))),
      Λ (Φ (τ (a ⊗ₜ residue _ v))) = Θ (a ⊗ₜ residue _ v) := by
    intro a v
    rw [hτ, α_residue]
    have eL : (a ⊗ₜ[(ResidueField O)] (σ p 𝔛 O k (algebraMap (ResidueField O) k)).hom v : k ⊗[(ResidueField O)] ↥(((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).functionField)) = (a ⊗ₜ 1) * (1 ⊗ₜ (σ p 𝔛 O k (algebraMap (ResidueField O) k)).hom v) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have eR : (a ⊗ₜ[O] residue _ v : k ⊗[O] (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₂ p 𝔛 O k (algebraMap (ResidueField O) k))))) = (a ⊗ₜ 1) * (1 ⊗ₜ residue _ v) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [eL, eR, map_mul, map_mul, map_mul, hΘk, hΘK]
    have hΦa : Φ (a ⊗ₜ 1) = algebraMap k ↥((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).functionField) a := Φ.commutes a
    rw [hΦa]
    change Λ (AlgebraicCurve.baseToFunctionField (pullback.snd ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) a) * _ = _
    rw [hΛ1]
    congr 1

    obtain ⟨W₀, hW₀, s₀, hs₀⟩ := (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.exists_germ_eq ((σ₁ p 𝔛 O k (algebraMap (ResidueField O) k)).hom v)
    let W : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens := W₀ ⊓ U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)
    have hW : ζ₂ p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) ∈ W := ⟨hW₀, ζ₂_mem_U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)⟩
    let sW : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.obj (Opposite.op W)) := ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.map (homOfLE inf_le_left).op) s₀
    have hσ₁ : (σ₁ p 𝔛 O k (algebraMap (ResidueField O) k)).hom v = ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.germ W (ζ₂ p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)) hW).hom sW := by
      rw [← hs₀]; exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
    have hW' : (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.base (genericPoint ↥((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) ∈ W := by rw [ι_genericPoint_U]; exact hW
    have hσ : (σ p 𝔛 O k (algebraMap (ResidueField O) k)).hom v =
        (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).presheaf.germ ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W) (genericPoint ↥((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) hW').hom (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.app W).hom sW) := by
      change (σ₂ p 𝔛 O k (algebraMap (ResidueField O) k)).hom ((σ₁ p 𝔛 O k (algebraMap (ResidueField O) k)).hom v) = _
      rw [hσ₁]
      exact σ₂_germ p 𝔛 O k (algebraMap (ResidueField O) k) W hW sW hW'
    rw [hσ]
    haveI ne1 : Nonempty (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W : ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).Opens) : Scheme.{0}) := ⟨⟨(genericPoint ↥((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})), hW'⟩⟩
    haveI ne2 : Nonempty (((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ⁻¹ᵁ ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W) : ((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).Opens) : Scheme.{0}) :=
      ⟨⟨genericPoint ↥(pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))), by
        change (pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).base (genericPoint ↥(pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))) ∈ (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W
        rw [π_genericPoint]; exact hW'⟩⟩
    have hgf : (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).presheaf.germ ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W) (genericPoint ↥((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) hW').hom (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.app W).hom sW) =
        ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).germToFunctionField ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W) (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.app W).hom sW) := rfl
    rw [hgf, hΦgerm ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W) (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.app W).hom sW), hΛ2 W hW sW]
    rw [Scheme.Hom.stalkMap_comp (𝔛.compZero k) (bck p (ResidueField O) k (algebraMap (ResidueField O) k) ≫ bc₀ p O)
      (genericPoint ↥(𝔛.ratModel k).C),
      Scheme.Hom.stalkMap_comp (bck p (ResidueField O) k (algebraMap (ResidueField O) k)) (bc₀ p O),
      Scheme.Hom.stalkMap_comp (𝔛.compZero k) (bck p (ResidueField O) k (algebraMap (ResidueField O) k))]
    change ((𝔛.compZero k).stalkMap _).hom (((bck p (ResidueField O) k (algebraMap (ResidueField O) k)).stalkMap _).hom _) =
      ((𝔛.compZero k).stalkMap _).hom (((bck p (ResidueField O) k (algebraMap (ResidueField O) k)).stalkMap _).hom
        ((σ₁ p 𝔛 O k (algebraMap (ResidueField O) k)).hom v))
    rw [hσ₁]

  have key : ∀ x, Θ x = Λ (Φ (τ x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, hτzero, map_zero, map_zero]
    | tmul a w =>
      obtain ⟨v, rfl⟩ := IsLocalRing.residue_surjective w
      exact (key1 a v).symm
    | add x y hx hy => rw [map_add, hx, hy, hτadd, map_add, map_add]
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · rw [key, key] at hxy
    exact hτbij.1 (hΦinj (Λ.injective hxy))
  · obtain ⟨w, rfl⟩ := hΛsurj z
    letI := Φ.toRingHom.toAlgebra
    haveI := hΦfrac
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := k ⊗[(ResidueField O)] ↥(((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).functionField)) w
    obtain ⟨a', rfl⟩ := hτbij.2 a
    obtain ⟨b', rfl⟩ := hτbij.2 b
    refine ⟨a', b', ?_, ?_⟩
    · rw [key]
      intro h0
      apply nonZeroDivisors.ne_zero hb
      apply hΦinj
      rw [map_zero]
      exact (map_eq_zero Λ).mp h0
    · rw [key, key, map_div₀]
      rfl

end Assembly
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.E87FF"

section Public

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
  (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (toκ : O →+* k)

include hϖ in
set_option maxHeartbeats 3200000 in
theorem injective_and_frac_compZero
    [algk : Algebra O k] (halgk : algebraMap O k = toκ)
    [algK : Algebra O (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C))))]
    (halgK : ∀ a : O, algebraMap O (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)))) a =
      residue _ (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)) trivial).hom
        (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a))))
    (Θ : k ⊗[O] (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)))) →+* ↥((𝔛.ratModel k).C.functionField))
    (hΘk : ∀ a : k, Θ (a ⊗ₜ 1) = AlgebraicCurve.baseToFunctionField (𝔛.ratModel k).toBase a)
    (hΘK : ∀ v : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
      Θ (1 ⊗ₜ residue _ v) = ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).stalkMap (genericPoint ↥(𝔛.ratModel k).C)).hom v)

    (Λpack : haveI : CharP (ResidueField O) p := charP_residueField p O hϖ
      ∀ (i : (ResidueField O) →+* k), i.comp (residue O) = toκ →
      letI : Algebra (ResidueField O) k := i.toAlgebra
      ∃ Λ : ↥((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).functionField) →+* ↥((𝔛.ratModel k).C.functionField),
        Function.Surjective Λ ∧
        (∀ a : k, Λ (AlgebraicCurve.baseToFunctionField
          (pullback.snd ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) a) =
          AlgebraicCurve.baseToFunctionField (𝔛.ratModel k).toBase a) ∧
        (∀ (W : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) (hW : ζ₂ p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) ∈ W) (s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.obj (Opposite.op W))
          [Nonempty (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W : ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).Opens) : Scheme.{0})]
          [Nonempty (((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ⁻¹ᵁ ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W) : ((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).Opens) : Scheme.{0})],
          Λ ((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).germToFunctionField ((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ⁻¹ᵁ ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W)) (((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).app ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W)).hom (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.app W).hom s))) =
            ((𝔛.compZero k ≫ bck p (ResidueField O) k (algebraMap (ResidueField O) k)).stalkMap (genericPoint ↥(𝔛.ratModel k).C)).hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.germ W (ζ₂ p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)) hW).hom s))) :
    Function.Injective Θ ∧ ∀ z : ↥((𝔛.ratModel k).C.functionField), ∃ a b, Θ b ≠ 0 ∧ z = Θ a / Θ b := by
  haveI : CharP (ResidueField O) p := charP_residueField p O hϖ
  haveI : IsLocalHom toκ := isLocalHom_toκ p O hϖ k toκ
  let i : (ResidueField O) →+* k := ResidueField.lift toκ
  have hi : i.comp (residue O) = toκ := ResidueField.lift_comp_residue toκ
  letI algk₀ : Algebra (ResidueField O) k := i.toAlgebra
  obtain ⟨Λ, hΛsurj, hΛ1, hΛ2⟩ := Λpack i hi
  have halgk' : algebraMap O k = (algebraMap (ResidueField O) k).comp (residue O) := by rw [halgk, ← hi]; rfl

  have E : DRModel.baseChangeMap (p := p) toκ = bck p (ResidueField O) k (algebraMap (ResidueField O) k) ≫ bc₀ p O := by
    rw [baseChangeMap_comp_baseChangeMap]
    congr 1
  clear_value i
  revert algK halgK Θ hΘk hΘK
  rw [E]
  intro algK halgK Θ hΘk hΘK
  exact core p 𝔛 O k hϖ halgk' (algK := algK) halgK Θ hΘk hΘK Λ hΛsurj hΛ1 hΛ2

end Public
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.E87FF"

section Lambda

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
  (k : Type) [Field k] [CharP k p] [IsAlgClosed k] [Algebra (ResidueField O) k] [CharP (ResidueField O) p]

theorem V_eq : (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) = ⟨(Set.range (𝔛.compInf k).base)ᶜ,
    (@Scheme.Hom.isClosedEmbedding _ _ (𝔛.compInf k) (𝔛.compInf_isClosedImmersion k)).isClosed_range.isOpen_compl⟩ :=
  TopologicalSpace.Opens.ext (coe_V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k))

scoped instance isOpenImmersion_restrict_compZero_V : IsOpenImmersion ((𝔛.compZero k ⁻¹ᵁ (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens)).ι ≫ 𝔛.compZero k) := by
  rw [V_eq]
  exact ModularCurve.DRModelPackage.isOpenImmersion_restrict_compZero_compl_range_compInf p 𝔛 k

scoped instance nonempty_preimage_V : Nonempty (𝔛.compZero k ⁻¹ᵁ (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : (𝔛.ratModel k).C.Opens) := by
  have hmem := sectionFibre_εzero_mem_V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)
  obtain ⟨c, hc⟩ := 𝔛.εzero_mem_compZero k ⟨IsLocalRing.closedPoint k, rfl⟩
  exact ⟨⟨c, show (𝔛.compZero k).base c ∈ (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) by rw [hc]; exact hmem⟩⟩

def eVU : ((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0}) ≅ (pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) := (isPullback_V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)).isoPullback

theorem eVU_hom_fst : (eVU p 𝔛 O k).hom ≫ (pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) = (bck p (ResidueField O) k (algebraMap (ResidueField O) k)) ∣_ (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)) :=
  (isPullback_V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)).isoPullback_hom_fst

theorem eVU_hom_snd : (eVU p 𝔛 O k).hom ≫ (pullback.snd ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) = (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) :=
  (isPullback_V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)).isoPullback_hom_snd

theorem eVU_hom_fst_ι : (eVU p 𝔛 O k).hom ≫ (pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ≫ (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι = (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens).ι ≫ bck p (ResidueField O) k (algebraMap (ResidueField O) k) := by
  rw [← Category.assoc, eVU_hom_fst, morphismRestrict_ι]

theorem eVU_genericPoint : (eVU p 𝔛 O k).hom.base (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) = (genericPoint ↥(pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))) :=
  genericPoint_eq_of_isOpenImmersion _

def Pfx : ((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).functionField ⟶ ((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0}).functionField :=
  (((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).presheaf.stalkCongr (.of_eq (eVU_genericPoint p 𝔛 O k).symm)).hom ≫
    (eVU p 𝔛 O k).hom.stalkMap (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0}))

scoped instance isIso_Pfx : IsIso (Pfx p 𝔛 O k) := by
  unfold Pfx; exact IsIso.comp_isIso

theorem Pfx_germ {Z : Scheme.{0}} (f : (pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ⟶ Z) (W : Z.Opens) (t : Γ(Z, W))
    (h₁ : f.base (genericPoint ↥(pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))) ∈ W) (h₂ : ((eVU p 𝔛 O k).hom ≫ f).base (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) ∈ W) :
    (Pfx p 𝔛 O k).hom ((((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).presheaf.germ (f ⁻¹ᵁ W) (genericPoint ↥(pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))) h₁).hom ((f.app W).hom t)) =
      (((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0}).presheaf.germ (((eVU p 𝔛 O k).hom ≫ f) ⁻¹ᵁ W) (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) h₂).hom ((((eVU p 𝔛 O k).hom ≫ f).app W).hom t) := by
  have h₁' : (eVU p 𝔛 O k).hom.base (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) ∈ f ⁻¹ᵁ W := h₂
  change ((eVU p 𝔛 O k).hom.stalkMap (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0}))).hom (((((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).presheaf.stalkCongr
    (.of_eq (eVU_genericPoint p 𝔛 O k).symm)).hom).hom ((((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).presheaf.germ (f ⁻¹ᵁ W) (genericPoint ↥(pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))) h₁).hom ((f.app W).hom t))) = _
  rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes_apply]
  erw [Scheme.Hom.germ_stalkMap_apply (eVU p 𝔛 O k).hom (f ⁻¹ᵁ W) (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) h₁']
  rfl

set_option maxHeartbeats 3200000 in

theorem Λpack_compZero :
    ∃ Λ : ↥((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).functionField) →+* ↥((𝔛.ratModel k).C.functionField),
      Function.Surjective Λ ∧
      (∀ a : k, Λ (AlgebraicCurve.baseToFunctionField (pullback.snd ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) a) =
        AlgebraicCurve.baseToFunctionField (𝔛.ratModel k).toBase a) ∧
      (∀ (W : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) (hW : ζ₂ p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) ∈ W) (s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.obj (Opposite.op W))
        [Nonempty (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W : ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).Opens) : Scheme.{0})]
        [Nonempty (((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ⁻¹ᵁ ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W) : ((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).Opens) : Scheme.{0})],
        Λ ((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).germToFunctionField ((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ⁻¹ᵁ ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W)) (((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).app ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W)).hom (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.app W).hom s))) =
          ((𝔛.compZero k ≫ bck p (ResidueField O) k (algebraMap (ResidueField O) k)).stalkMap (genericPoint ↥(𝔛.ratModel k).C)).hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.germ W (ζ₂ p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)) hW).hom s)) := by
  let Λ0 := E87FF.Λ (𝔛.compZero k) (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens)
  refine ⟨(Pfx p 𝔛 O k ≫ Λ0.hom).hom, ?_, ?_, ?_⟩
  · exact (ConcreteCategory.bijective_of_isIso (Pfx p 𝔛 O k ≫ Λ0.hom)).2
  ·
    intro a
    have hV1 : (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens).ι.base (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) ∈ (⊤ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) := trivial
    have hC1 : (𝔛.compZero k).base (genericPoint ↥(𝔛.ratModel k).C) ∈ (⊤ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) := trivial
    change Λ0.hom.hom ((Pfx p 𝔛 O k).hom ((((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).presheaf.germ ⊤ (genericPoint ↥(pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))) trivial).hom
      (((pullback.snd ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)))) = _
    have step1 := Pfx_germ p 𝔛 O k (pullback.snd ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a) trivial trivial
    erw [step1]
    have step2 := E87FF.germ_app_congr (eVU_hom_snd p 𝔛 O k) ⊤ (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) trivial trivial ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a)
    erw [step2]
    have step3 := E87FF.Λ_germ (𝔛.compZero k) (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) ⊤ (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)) hV1 hC1
    erw [step3]

    have step4 := E87FF.germ_app_congr (𝔛.compZero_over k) ⊤ (genericPoint ↥(𝔛.ratModel k).C) trivial trivial ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a)
    simp only [Scheme.Hom.comp_app] at step4
    exact step4
  · intro W hW s _ _
    have hgenU : (pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).base (genericPoint ↥(pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))) ∈ (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W := by
      change _ ∈ (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W; rw [π_genericPoint]
      change (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.base _ ∈ W; rw [ι_genericPoint_U]; exact hW
    have hζ : (𝔛.compZero k ≫ bck p (ResidueField O) k (algebraMap (ResidueField O) k)).base (genericPoint ↥(𝔛.ratModel k).C) ∈ W := hW
    have hVW : ((eVU p 𝔛 O k).hom ≫ (pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ≫ (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι).base (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) ∈ W := by
      rw [eVU_hom_fst_ι]
      change (bck p (ResidueField O) k (algebraMap (ResidueField O) k)).base ((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens).ι.base (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0}))) ∈ W
      rw [E87FF.ι_genericPoint_eq (𝔛.compZero k) (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens)]
      exact hζ
    change Λ0.hom.hom ((Pfx p 𝔛 O k).hom ((((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).presheaf.germ (((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ≫ (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι) ⁻¹ᵁ W) (genericPoint ↥(pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))) hgenU).hom
      ((((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ≫ (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι).app W).hom s))) = _
    have step1 := Pfx_germ p 𝔛 O k ((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ≫ (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι) W s hgenU hVW
    erw [step1]
    have hVW' : ((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens).ι ≫ bck p (ResidueField O) k (algebraMap (ResidueField O) k)).base (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) ∈ W := by rw [← eVU_hom_fst_ι]; exact hVW
    have step2 := E87FF.germ_app_congr (eVU_hom_fst_ι p 𝔛 O k) W (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) hVW hVW' s
    erw [step2]
    have hV1 : (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens).ι.base (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) ∈ (bck p (ResidueField O) k (algebraMap (ResidueField O) k)) ⁻¹ᵁ W := hVW'
    have hC1 : (𝔛.compZero k).base (genericPoint ↥(𝔛.ratModel k).C) ∈ (bck p (ResidueField O) k (algebraMap (ResidueField O) k)) ⁻¹ᵁ W := hζ
    have step3 := E87FF.Λ_germ (𝔛.compZero k) (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) ((bck p (ResidueField O) k (algebraMap (ResidueField O) k)) ⁻¹ᵁ W)
      (((bck p (ResidueField O) k (algebraMap (ResidueField O) k)).app W).hom s) hV1 hC1
    erw [step3]

    have step4 := Scheme.Hom.germ_stalkMap_apply (𝔛.compZero k ≫ bck p (ResidueField O) k (algebraMap (ResidueField O) k)) W
      (genericPoint ↥(𝔛.ratModel k).C) hζ s
    erw [step4]
    first
      | rfl
      | (simp only [Scheme.Hom.comp_app]; rfl)

end Lambda
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.E87FF"

section Final

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
  (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (toκ : O →+* k)

include hϖ in

theorem dock_compZero
    [algk : Algebra O k] (halgk : algebraMap O k = toκ)
    [algK : Algebra O (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C))))]
    (halgK : ∀ a : O, algebraMap O (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)))) a =
      residue _ (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)) trivial).hom
        (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a))))
    (Θ : k ⊗[O] (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)))) →+* ↥((𝔛.ratModel k).C.functionField))
    (hΘk : ∀ a : k, Θ (a ⊗ₜ 1) = AlgebraicCurve.baseToFunctionField (𝔛.ratModel k).toBase a)
    (hΘK : ∀ v : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
      Θ (1 ⊗ₜ residue _ v) = ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).stalkMap (genericPoint ↥(𝔛.ratModel k).C)).hom v) :
    Function.Injective Θ ∧ ∀ z : ↥((𝔛.ratModel k).C.functionField), ∃ a b, Θ b ≠ 0 ∧ z = Θ a / Θ b :=
  injective_and_frac_compZero p 𝔛 O hϖ k toκ halgk halgK Θ hΘk hΘK (fun i _ => by
    haveI : CharP (ResidueField O) p := charP_residueField p O hϖ
    letI : Algebra (ResidueField O) k := i.toAlgebra
    exact Λpack_compZero p 𝔛 O k)

end Final
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.E87FF"

namespace Inf

section OpenPiece

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (k₀ : Type) [Field k₀] [CharP k₀ p]
  (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (i : k₀ →+* k)

def U : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))).Opens :=
  ⟨(closure {ζ₂ p 𝔛 k₀ k i})ᶜ, isClosed_closure.isOpen_compl⟩

theorem mem_U_iff (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀))))) : x ∈ U p 𝔛 k₀ k i ↔ x ∉ closure {ζ₂ p 𝔛 k₀ k i} := Iff.rfl

theorem ζ₁_mem_U : ζ₁ p 𝔛 k₀ k i ∈ U p 𝔛 k₀ k i := ζ₁_not_mem_closure_ζ₂ p 𝔛 k₀ k i

theorem U_subset_closure_ζ₁ : ((U p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))).Opens) : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀))))) ⊆ closure {ζ₁ p 𝔛 k₀ k i} := by
  intro x hx
  have := (Set.eq_univ_iff_forall.mp (closure_ζ₁_union_closure_ζ₂ p 𝔛 k₀ k i)) x
  rcases this with h | h
  · exact h
  · exact absurd h hx

theorem closure_U_eq : closure ((U p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))).Opens) : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀))))) = closure {ζ₁ p 𝔛 k₀ k i} := by
  refine le_antisymm (closure_minimal (U_subset_closure_ζ₁ p 𝔛 k₀ k i) isClosed_closure) ?_
  exact closure_mono (Set.singleton_subset_iff.mpr (ζ₁_mem_U p 𝔛 k₀ k i))

scoped instance irreducibleSpace_U : IrreducibleSpace ↥(U p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))).Opens) := by
  have hirr : IsIrreducible ((U p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))).Opens) : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀))))) :=
    ⟨⟨_, ζ₁_mem_U p 𝔛 k₀ k i⟩,
      (isIrreducible_singleton.closure : IsIrreducible (closure {ζ₁ p 𝔛 k₀ k i})).2.open_subset
        (U p 𝔛 k₀ k i).isOpen (U_subset_closure_ζ₁ p 𝔛 k₀ k i)⟩
  exact Subtype.irreducibleSpace hirr

scoped instance isIntegral_U : IsIntegral (U p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))).Opens) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : IsReduced (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))) := ModularCurve.DRModel.isReduced_pullback_toBase_of_charP p k₀
  haveI : IsReduced (U p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))).Opens) := isReduced_of_isOpenImmersion (U p 𝔛 k₀ k i).ι
  haveI : IrreducibleSpace ↥((U p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))).Opens) : Scheme.{0}) := irreducibleSpace_U p 𝔛 k₀ k i
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem ι_genericPoint_U :
    (U p 𝔛 k₀ k i).ι.base (genericPoint ↥((U p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))).Opens) : Scheme.{0})) = ζ₁ p 𝔛 k₀ k i := by
  have h1 := (genericPoint_spec ↥((U p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀)))).Opens) : Scheme.{0})).image
    (U p 𝔛 k₀ k i).ι.base.hom.continuous
  rw [Set.image_univ, Scheme.Opens.range_ι, closure_U_eq] at h1
  exact h1.eq isGenericPoint_closure

end OpenPiece
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.E87FF"

section BaseChangeOpen

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (k₀ : Type) [Field k₀] [CharP k₀ p]
  (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (i : k₀ →+* k)

abbrev V : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens := (bck p k₀ k i) ⁻¹ᵁ (U p 𝔛 k₀ k i)

theorem coe_V : ((V p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))) = (Set.range (𝔛.compZero k).base)ᶜ := by
  change (bck p k₀ k i).base ⁻¹' (closure {ζ₂ p 𝔛 k₀ k i})ᶜ = _
  rw [Set.preimage_compl, preimage_closure_ζ₂]

theorem mem_V_iff (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))) : y ∈ V p 𝔛 k₀ k i ↔ y ∉ Set.range (𝔛.compZero k).base := by
  rw [← SetLike.mem_coe, coe_V]; rfl

theorem V_subset_range_compInf : ((V p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))) ⊆ Set.range (𝔛.compInf k).base := by
  intro y hy
  rw [coe_V] at hy
  exact (𝔛.comp_jointly_surjective k y).resolve_right hy

theorem sectionFibre_εinf_mem_V :
    (DRModel.sectionFibre 𝔛.εinf (algebraMap ℤ k)).base (IsLocalRing.closedPoint k) ∈ V p 𝔛 k₀ k i := by
  rw [mem_V_iff]
  intro hI
  have hZ : (DRModel.sectionFibre 𝔛.εinf (algebraMap ℤ k)).base (IsLocalRing.closedPoint k) ∈ Set.range (𝔛.compInf k).base :=
    𝔛.εinf_mem_compInf k ⟨IsLocalRing.closedPoint k, rfl⟩
  have hsm : (DRModel.sectionFibre 𝔛.εinf (algebraMap ℤ k)).base (IsLocalRing.closedPoint k) ∈
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) ⁻¹ᵁ 𝔛.smoothLocus) := by
    change (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base
      ((DRModel.sectionFibre 𝔛.εinf (algebraMap ℤ k)).base (IsLocalRing.closedPoint k)) ∈ (𝔛.smoothLocus : Set (DRModel p))
    rw [← TopCat.comp_app, ← Scheme.Hom.comp_base, DRModel.sectionFibre, pullback.lift_fst, Scheme.Hom.comp_base, TopCat.comp_app]
    exact 𝔛.εinf_mem_smoothLocus ⟨_, rfl⟩
  exact ((ModularCurve.DRModelPackage.mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero p 𝔛 k _).mp hsm)
    ⟨hZ, hI⟩

scoped instance irreducibleSpace_V : IrreducibleSpace ↥(V p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) := by
  have hirr : IsIrreducible ((V p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))) := by
    refine ⟨⟨_, sectionFibre_εinf_mem_V p 𝔛 k₀ k i⟩, ?_⟩
    have hZ : IsIrreducible (Set.range (𝔛.compInf k).base) := by
      rw [range_compInf_eq_closure]; exact isIrreducible_singleton.closure
    exact hZ.2.open_subset (V p 𝔛 k₀ k i).isOpen (V_subset_range_compInf p 𝔛 k₀ k i)
  exact Subtype.irreducibleSpace hirr

scoped instance isIntegral_V : IsIntegral (V p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : IsReduced (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) := ModularCurve.DRModel.isReduced_pullback_toBase_of_charP p k
  haveI : IsReduced (V p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) := isReduced_of_isOpenImmersion (V p 𝔛 k₀ k i).ι
  haveI : IrreducibleSpace ↥((V p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0}) := irreducibleSpace_V p 𝔛 k₀ k i
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem isPullback_V :
    IsPullback ((bck p k₀ k i) ∣_ (U p 𝔛 k₀ k i))
      ((V p 𝔛 k₀ k i).ι ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))
      ((U p 𝔛 k₀ k i).ι ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀))))
      (Spec.map (CommRingCat.ofHom i)) :=
  (isPullback_morphismRestrict (bck p k₀ k i) (U p 𝔛 k₀ k i)).paste_vert (isPullback_baseChangeMap p i)

theorem isIntegral_pullback_U :
    letI : Algebra k₀ k := i.toAlgebra
    IsIntegral ↑(pullback ((U p 𝔛 k₀ k i).ι ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀))))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k)))) := by
  letI : Algebra k₀ k := i.toAlgebra
  let e := (isPullback_V p 𝔛 k₀ k i).isoPullback
  haveI : IsIntegral (V p 𝔛 k₀ k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) := isIntegral_V p 𝔛 k₀ k i
  haveI : IrreducibleSpace ↥(pullback ((U p 𝔛 k₀ k i).ι ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀))))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k)))) :=
    (Homeomorph.irreducibleSpace_iff (Scheme.homeoOfIso e)).mp inferInstance
  haveI : IsReduced (pullback ((U p 𝔛 k₀ k i).ι ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k₀))))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k)))) := isReduced_of_isOpenImmersion e.inv
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end BaseChangeOpen
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.E87FF"

section ResidueField

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
  (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (i : ResidueField O →+* k)

abbrev bc₀ := DRModel.baseChangeMap (p := p) (residue O)

scoped instance isClosedImmersion_bc₀ : IsClosedImmersion (bc₀ p O) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (residue O))) :=
    IsClosedImmersion.spec_of_surjective _ (by simpa using IsLocalRing.residue_surjective)
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_baseChangeMap p (residue O)).flip inferInstance

variable [CharP (ResidueField O) p]

abbrev ξ₁ : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) := (bc₀ p O).base (ζ₁ p 𝔛 (ResidueField O) k i)

abbrev σ₁ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₁ p 𝔛 O k i) ⟶
    (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.stalk (ζ₁ p 𝔛 (ResidueField O) k i) :=
  (bc₀ p O).stalkMap (ζ₁ p 𝔛 (ResidueField O) k i)

theorem σ₁_surjective : Function.Surjective (σ₁ p 𝔛 O k i) :=
  (bc₀ p O).stalkMap_surjective _

def ιStalkIso : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.stalk ((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.base (genericPoint ↥((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}))) ≅
    (U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).toScheme.presheaf.stalk (genericPoint ↥((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) :=
  @asIso _ _ _ _ ((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.stalkMap (genericPoint ↥((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})))
    (inferInstanceAs <| IsIso ((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.toLRSHom.stalkMap (genericPoint ↥((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}))))

theorem ιStalkIso_hom : (ιStalkIso p 𝔛 O k i).hom = (U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.stalkMap (genericPoint ↥((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) := rfl

abbrev σ₂ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.stalk (ζ₁ p 𝔛 (ResidueField O) k i) ⟶
    (U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).toScheme.presheaf.stalk (genericPoint ↥((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) :=
  ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.stalkCongr (.of_eq (ι_genericPoint_U p 𝔛 (ResidueField O) k i).symm)).hom ≫
    (ιStalkIso p 𝔛 O k i).hom

scoped instance isIso_σ₂ : IsIso (σ₂ p 𝔛 O k i) := IsIso.comp_isIso

abbrev σ := σ₁ p 𝔛 O k i ≫ σ₂ p 𝔛 O k i

theorem σ_surjective : Function.Surjective (σ p 𝔛 O k i) :=
  (ConcreteCategory.bijective_of_isIso (σ₂ p 𝔛 O k i)).2.comp (σ₁_surjective p 𝔛 O k i)

scoped instance isLocalHom_σ : IsLocalHom (σ p 𝔛 O k i).hom := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hmem : a ∈ maximalIdeal _ := by rwa [mem_maximalIdeal, mem_nonunits_iff]
  have h1 : ((bc₀ p O).stalkMap (ζ₁ p 𝔛 (ResidueField O) k i)).hom a ∈ maximalIdeal _ :=
    map_nonunit ((bc₀ p O).stalkMap (ζ₁ p 𝔛 (ResidueField O) k i)).hom a hmem

  have eS : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.stalk (ζ₁ p 𝔛 (ResidueField O) k i) ≃+* ↥(((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).functionField) := (asIso (σ₂ p 𝔛 O k i)).commRingCatIsoToRingEquiv
  have hSf : IsField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.stalk (ζ₁ p 𝔛 (ResidueField O) k i)) := MulEquiv.isField (Field.toIsField ↥(((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).functionField)) eS.toMulEquiv
  have h1' : ((bc₀ p O).stalkMap (ζ₁ p 𝔛 (ResidueField O) k i)).hom a = 0 := by
    have hnu : ¬ IsUnit (((bc₀ p O).stalkMap (ζ₁ p 𝔛 (ResidueField O) k i)).hom a) := (mem_maximalIdeal _).mp h1
    by_contra hne
    obtain ⟨b, hb⟩ := hSf.mul_inv_cancel hne
    exact hnu (isUnit_iff_exists_inv.mpr ⟨b, hb⟩)
  have : (σ p 𝔛 O k i).hom a = 0 := by
    change (σ₂ p 𝔛 O k i).hom (((bc₀ p O).stalkMap (ζ₁ p 𝔛 (ResidueField O) k i)).hom a) = 0
    rw [h1']
    exact map_zero _
  rw [this] at ha
  exact not_isUnit_zero ha

def α : ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₁ p 𝔛 O k i)) →+*
    ↥(((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).functionField) :=
  ResidueField.lift (σ p 𝔛 O k i).hom

theorem α_residue (v : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₁ p 𝔛 O k i)) :
    α p 𝔛 O k i (residue _ v) = (σ p 𝔛 O k i).hom v :=
  ResidueField.lift_residue_apply _ v

theorem α_bijective : Function.Bijective (α p 𝔛 O k i) := by
  refine ⟨(α p 𝔛 O k i).injective, fun y => ?_⟩
  obtain ⟨v, rfl⟩ := σ_surjective p 𝔛 O k i y
  exact ⟨residue _ v, α_residue p 𝔛 O k i v⟩

abbrev constO (ξ : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) : O →+* (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ :=
  ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ ξ trivial).hom.comp
    (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)

theorem not_isUnit_constO_natCast : ¬ IsUnit (constO p O (ξ₁ p 𝔛 O k i) ((p : ℕ) : O)) := by
  intro hu
  apply ModularCurve.DRModel.baseChangeMap_apply_notMem_preimage_basicOpen p O (ResidueField O) (residue O)
    (ζ₁ p 𝔛 (ResidueField O) k i)
  have h1 : (ξ₁ p 𝔛 O k i) ∈ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).basicOpen
      ((((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ⊤).hom
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ((p : ℕ) : O)))) :=
    ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).mem_basicOpen (U := ⊤) _ (ξ₁ p 𝔛 O k i) trivial).mpr hu
  rw [← Scheme.preimage_basicOpen] at h1
  erw [basicOpen_eq_of_affine] at h1
  exact h1

theorem isLocalHom_constO (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)}) :
    IsLocalHom (constO p O (ξ₁ p 𝔛 O k i)) := by
  refine ⟨fun o ho => ?_⟩
  by_contra hno
  have hmem : o ∈ maximalIdeal O := by rwa [mem_maximalIdeal, mem_nonunits_iff]
  rw [hϖ, Ideal.mem_span_singleton] at hmem
  obtain ⟨t, rfl⟩ := hmem
  rw [map_mul] at ho
  exact not_isUnit_constO_natCast p 𝔛 O k i (isUnit_of_mul_isUnit_left ho)

variable (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)})

def j : ResidueField O →+* ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₁ p 𝔛 O k i)) :=
  @ResidueField.map _ _ _ _ _ _ (constO p O (ξ₁ p 𝔛 O k i)) (isLocalHom_constO p 𝔛 O k i hϖ)

theorem j_residue (o : O) : j p 𝔛 O k i hϖ (residue O o) = residue _ (constO p O (ξ₁ p 𝔛 O k i) o) := by
  haveI := isLocalHom_constO p 𝔛 O k i hϖ
  exact ResidueField.map_residue _ o

theorem α_residue_constO (o : O) :
    α p 𝔛 O k i (residue _ (constO p O (ξ₁ p 𝔛 O k i) o)) =
      AlgebraicCurve.baseToFunctionField ((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ pullback.snd (DRModel.toBase p)
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))) (residue O o) := by
  rw [α_residue]

  change (σ₂ p 𝔛 O k i).hom (((bc₀ p O).stalkMap (ζ₁ p 𝔛 (ResidueField O) k i)).hom
    (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ (ξ₁ p 𝔛 O k i) trivial).hom
      (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)))) = _
  erw [Scheme.Hom.germ_stalkMap_apply (bc₀ p O) ⊤ (ζ₁ p 𝔛 (ResidueField O) k i) trivial]

  have hsq : ((bc₀ p O).app ⊤).hom ((((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
      ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) =
      ((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (ResidueField O))).inv.hom (residue O o)) := by
    have h := congrArg (fun φ => (Scheme.Hom.appTop φ).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o))
      (baseChangeMap_snd p (residue O))
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
    have hnat := congrArg (fun φ => φ.hom o) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (residue O)))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at hnat
    rw [← hnat] at h
    exact h
  erw [hsq]

  change (ιStalkIso p 𝔛 O k i).hom.hom ((((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.stalkCongr
      (.of_eq (ι_genericPoint_U p 𝔛 (ResidueField O) k i).symm)).hom).hom
    (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.germ ⊤ (ζ₁ p 𝔛 (ResidueField O) k i) trivial).hom _)) = _
  rw [TopCat.Presheaf.stalkCongr_hom, ← CommRingCat.comp_apply ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.germ ⊤ _ trivial),
    TopCat.Presheaf.germ_stalkSpecializes]
  rw [ιStalkIso_hom]
  erw [Scheme.Hom.germ_stalkMap_apply (U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⊤ (genericPoint ↥((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) trivial]
  rfl

theorem σ₂_germ (W : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) (hW : ζ₁ p 𝔛 (ResidueField O) k i ∈ W)
    (s : Γ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))), W)) (hW' : (U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.base (genericPoint ↥((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) ∈ W) :
    (σ₂ p 𝔛 O k i).hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.germ W (ζ₁ p 𝔛 (ResidueField O) k i) hW).hom s) =
      (((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).presheaf.germ ((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W) (genericPoint ↥((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) hW').hom (((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.app W).hom s) := by
  change (ιStalkIso p 𝔛 O k i).hom.hom ((((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.stalkCongr
      (.of_eq (ι_genericPoint_U p 𝔛 (ResidueField O) k i).symm)).hom).hom
    (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.germ W (ζ₁ p 𝔛 (ResidueField O) k i) hW).hom s)) = _
  rw [TopCat.Presheaf.stalkCongr_hom, ← CommRingCat.comp_apply ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.germ W _ hW),
    TopCat.Presheaf.germ_stalkSpecializes (hy := hW) (h := (Inseparable.of_eq (ι_genericPoint_U p 𝔛 (ResidueField O) k i).symm).ge)]
  rw [ιStalkIso_hom]
  erw [Scheme.Hom.germ_stalkMap_apply (U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι W (genericPoint ↥((U p 𝔛 (ResidueField O) k i : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) hW']

end ResidueField
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.E87FF"

theorem base_genericPoint_eq_of_flat {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    f.base (genericPoint X) = genericPoint Y := by
  have hgen := Flat.generalizingMap f
  have hsp : genericPoint Y ⤳ f.base (genericPoint X) := genericPoint_specializes _
  obtain ⟨x', hx', hfx'⟩ := hgen hsp
  have hx'' : genericPoint X ⤳ x' := genericPoint_specializes _
  have heq : x' = genericPoint X := (hx'.antisymm hx'').eq
  rw [← hfx', heq]

section Assembly

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
  (k : Type) [Field k] [CharP k p] [IsAlgClosed k] [Algebra (ResidueField O) k] [CharP (ResidueField O) p]
  (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)})

scoped instance isIntegral_Uk : IsIntegral (pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) :=
  isIntegral_pullback_U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)

scoped instance flat_π : Flat (pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) := MorphismProperty.pullback_fst _ _ inferInstance

theorem π_genericPoint : (pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).base (genericPoint ↥(pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))) = (genericPoint ↥((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) :=
  base_genericPoint_eq_of_flat _

include hϖ in
set_option maxHeartbeats 6400000 in

theorem core
    [algk : Algebra O k] (halgk : algebraMap O k = (algebraMap (ResidueField O) k).comp (residue O))
    [algK : Algebra O (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₁ p 𝔛 O k (algebraMap (ResidueField O) k))))]
    (halgK : ∀ a : O, algebraMap O (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₁ p 𝔛 O k (algebraMap (ResidueField O) k)))) a = residue _ (constO p O (ξ₁ p 𝔛 O k (algebraMap (ResidueField O) k)) a))
    (Θ : k ⊗[O] (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₁ p 𝔛 O k (algebraMap (ResidueField O) k)))) →+* ↥((𝔛.ratModel k).C.functionField))
    (hΘk : ∀ a : k, Θ (a ⊗ₜ 1) = AlgebraicCurve.baseToFunctionField (𝔛.ratModel k).toBase a)
    (hΘK : ∀ v : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₁ p 𝔛 O k (algebraMap (ResidueField O) k)),
      Θ (1 ⊗ₜ residue _ v) = (((𝔛.compInf k ≫ (bck p (ResidueField O) k (algebraMap (ResidueField O) k) ≫ bc₀ p O)).stalkMap (genericPoint ↥(𝔛.ratModel k).C)).hom v))
    (Λ : ↥((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).functionField) →+* ↥((𝔛.ratModel k).C.functionField))
    (hΛsurj : Function.Surjective Λ)
    (hΛ1 : ∀ a : k, Λ (AlgebraicCurve.baseToFunctionField
        (pullback.snd ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) a) =
        AlgebraicCurve.baseToFunctionField (𝔛.ratModel k).toBase a)
    (hΛ2 : ∀ (W : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) (hW : ζ₁ p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) ∈ W) (s : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.obj (Opposite.op W)))
        [Nonempty (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W : ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).Opens) : Scheme.{0})]
        [Nonempty (((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ⁻¹ᵁ ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W) : ((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).Opens) : Scheme.{0})],
        Λ ((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).germToFunctionField ((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ⁻¹ᵁ ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W)) (((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).app ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W)).hom (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.app W).hom s))) =
          ((𝔛.compInf k ≫ bck p (ResidueField O) k (algebraMap (ResidueField O) k)).stalkMap (genericPoint ↥(𝔛.ratModel k).C)).hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.germ W (ζ₁ p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)) hW).hom s)) :
    Function.Injective Θ ∧ ∀ z : ↥((𝔛.ratModel k).C.functionField), ∃ a b, Θ b ≠ 0 ∧ z = Θ a / Θ b := by

  classical

  letI algKU : Algebra (ResidueField O) ↥(((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).functionField) := (AlgebraicCurve.baseToFunctionField ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))))).toAlgebra
  letI algkUk : Algebra k ↥((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).functionField) :=
    (AlgebraicCurve.baseToFunctionField (pullback.snd ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).toAlgebra

  obtain ⟨Φ, hΦinj, hΦfrac, hΦgerm⟩ :=
    AlgebraicGeometry.exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing k ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))))

  letI algK₀ : Algebra (ResidueField O) (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₁ p 𝔛 O k (algebraMap (ResidueField O) k)))) := (j p 𝔛 O k (algebraMap (ResidueField O) k) hϖ).toAlgebra
  haveI towK : IsScalarTower O (ResidueField O) (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₁ p 𝔛 O k (algebraMap (ResidueField O) k)))) := IsScalarTower.of_algebraMap_eq (fun o => by
    rw [halgK]; exact (j_residue p 𝔛 O k (algebraMap (ResidueField O) k) hϖ o).symm)
  haveI towk : IsScalarTower O (ResidueField O) k := IsScalarTower.of_algebraMap_eq (fun o => by
    rw [halgk]; rfl)

  let αe : (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₁ p 𝔛 O k (algebraMap (ResidueField O) k)))) ≃ₐ[(ResidueField O)] ↥(((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).functionField) :=
    AlgEquiv.ofBijective
      { (α p 𝔛 O k (algebraMap (ResidueField O) k)) with
        commutes' := fun r => by
          obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective r
          change α p 𝔛 O k (algebraMap (ResidueField O) k) (j p 𝔛 O k (algebraMap (ResidueField O) k) hϖ (residue O o)) = algebraMap (ResidueField O) ↥(((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).functionField) (residue O o)
          rw [j_residue, α_residue_constO p 𝔛 O k (algebraMap (ResidueField O) k) o]
          rfl }
      (α_bijective p 𝔛 O k (algebraMap (ResidueField O) k))
  have hαe : ∀ v, αe v = α p 𝔛 O k (algebraMap (ResidueField O) k) v := fun v => rfl

  haveI cs1 : TensorProduct.CompatibleSMul O (ResidueField O) k (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₁ p 𝔛 O k (algebraMap (ResidueField O) k)))) := ⟨fun r a v => by
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective r
    have h1 : (residue O o) • a = o • a := IsScalarTower.algebraMap_smul (ResidueField O) o a
    have h2 : (residue O o) • v = o • v := IsScalarTower.algebraMap_smul (ResidueField O) o v
    rw [h1, h2, TensorProduct.smul_tmul]⟩
  haveI cs2 : TensorProduct.CompatibleSMul (ResidueField O) O k (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₁ p 𝔛 O k (algebraMap (ResidueField O) k)))) := ⟨fun o a v => by
    have h1 : (residue O o) • a = o • a := IsScalarTower.algebraMap_smul (ResidueField O) o a
    have h2 : (residue O o) • v = o • v := IsScalarTower.algebraMap_smul (ResidueField O) o v
    rw [← h1, ← h2, TensorProduct.smul_tmul]⟩
  let B : k ⊗[O] (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₁ p 𝔛 O k (algebraMap (ResidueField O) k)))) ≃ₗ[O] k ⊗[(ResidueField O)] (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₁ p 𝔛 O k (algebraMap (ResidueField O) k)))) := TensorProduct.equivOfCompatibleSMul (ResidueField O) O O k (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₁ p 𝔛 O k (algebraMap (ResidueField O) k))))
  have hB : ∀ a v, B (a ⊗ₜ v) = a ⊗ₜ v := fun a v => rfl
  let M : k ⊗[(ResidueField O)] (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₁ p 𝔛 O k (algebraMap (ResidueField O) k)))) ≃ₐ[(ResidueField O)] k ⊗[(ResidueField O)] ↥(((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).functionField) := Algebra.TensorProduct.congr AlgEquiv.refl αe
  have hM : ∀ a v, M (a ⊗ₜ v) = a ⊗ₜ α p 𝔛 O k (algebraMap (ResidueField O) k) v := fun a v => by
    change Algebra.TensorProduct.map _ _ (a ⊗ₜ v) = _
    rw [Algebra.TensorProduct.map_tmul]
    rfl

  let τ : k ⊗[O] (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₁ p 𝔛 O k (algebraMap (ResidueField O) k)))) → k ⊗[(ResidueField O)] ↥(((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).functionField) := fun x => M (B x)
  have hτ : ∀ a v, τ (a ⊗ₜ v) = a ⊗ₜ α p 𝔛 O k (algebraMap (ResidueField O) k) v := fun a v => by
    change M (B (a ⊗ₜ v)) = _; rw [hB, hM]
  have hτbij : Function.Bijective τ := M.bijective.comp B.bijective
  have hτadd : ∀ x y, τ (x + y) = τ x + τ y := fun x y => by change M (B (x + y)) = _; rw [map_add, map_add]
  have hτzero : τ 0 = 0 := by change M (B 0) = 0; rw [map_zero, map_zero]

  have key1 : ∀ (a : k) (v : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₁ p 𝔛 O k (algebraMap (ResidueField O) k))),
      Λ (Φ (τ (a ⊗ₜ residue _ v))) = Θ (a ⊗ₜ residue _ v) := by
    intro a v
    rw [hτ, α_residue]
    have eL : (a ⊗ₜ[(ResidueField O)] (σ p 𝔛 O k (algebraMap (ResidueField O) k)).hom v : k ⊗[(ResidueField O)] ↥(((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).functionField)) = (a ⊗ₜ 1) * (1 ⊗ₜ (σ p 𝔛 O k (algebraMap (ResidueField O) k)).hom v) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have eR : (a ⊗ₜ[O] residue _ v : k ⊗[O] (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (ξ₁ p 𝔛 O k (algebraMap (ResidueField O) k))))) = (a ⊗ₜ 1) * (1 ⊗ₜ residue _ v) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [eL, eR, map_mul, map_mul, map_mul, hΘk, hΘK]
    have hΦa : Φ (a ⊗ₜ 1) = algebraMap k ↥((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).functionField) a := Φ.commutes a
    rw [hΦa]
    change Λ (AlgebraicCurve.baseToFunctionField (pullback.snd ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) a) * _ = _
    rw [hΛ1]
    congr 1

    obtain ⟨W₀, hW₀, s₀, hs₀⟩ := (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.exists_germ_eq ((σ₁ p 𝔛 O k (algebraMap (ResidueField O) k)).hom v)
    let W : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens := W₀ ⊓ U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)
    have hW : ζ₁ p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) ∈ W := ⟨hW₀, ζ₁_mem_U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)⟩
    let sW : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.obj (Opposite.op W)) := ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.map (homOfLE inf_le_left).op) s₀
    have hσ₁ : (σ₁ p 𝔛 O k (algebraMap (ResidueField O) k)).hom v = ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.germ W (ζ₁ p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)) hW).hom sW := by
      rw [← hs₀]; exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
    have hW' : (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.base (genericPoint ↥((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) ∈ W := by rw [ι_genericPoint_U]; exact hW
    have hσ : (σ p 𝔛 O k (algebraMap (ResidueField O) k)).hom v =
        (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).presheaf.germ ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W) (genericPoint ↥((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) hW').hom (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.app W).hom sW) := by
      change (σ₂ p 𝔛 O k (algebraMap (ResidueField O) k)).hom ((σ₁ p 𝔛 O k (algebraMap (ResidueField O) k)).hom v) = _
      rw [hσ₁]
      exact σ₂_germ p 𝔛 O k (algebraMap (ResidueField O) k) W hW sW hW'
    rw [hσ]
    haveI ne1 : Nonempty (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W : ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).Opens) : Scheme.{0}) := ⟨⟨(genericPoint ↥((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})), hW'⟩⟩
    haveI ne2 : Nonempty (((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ⁻¹ᵁ ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W) : ((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).Opens) : Scheme.{0}) :=
      ⟨⟨genericPoint ↥(pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))), by
        change (pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).base (genericPoint ↥(pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))) ∈ (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W
        rw [π_genericPoint]; exact hW'⟩⟩
    have hgf : (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).presheaf.germ ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W) (genericPoint ↥((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0})) hW').hom (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.app W).hom sW) =
        ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).germToFunctionField ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W) (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.app W).hom sW) := rfl
    rw [hgf, hΦgerm ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W) (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.app W).hom sW), hΛ2 W hW sW]
    rw [Scheme.Hom.stalkMap_comp (𝔛.compInf k) (bck p (ResidueField O) k (algebraMap (ResidueField O) k) ≫ bc₀ p O)
      (genericPoint ↥(𝔛.ratModel k).C),
      Scheme.Hom.stalkMap_comp (bck p (ResidueField O) k (algebraMap (ResidueField O) k)) (bc₀ p O),
      Scheme.Hom.stalkMap_comp (𝔛.compInf k) (bck p (ResidueField O) k (algebraMap (ResidueField O) k))]
    change ((𝔛.compInf k).stalkMap _).hom (((bck p (ResidueField O) k (algebraMap (ResidueField O) k)).stalkMap _).hom _) =
      ((𝔛.compInf k).stalkMap _).hom (((bck p (ResidueField O) k (algebraMap (ResidueField O) k)).stalkMap _).hom
        ((σ₁ p 𝔛 O k (algebraMap (ResidueField O) k)).hom v))
    rw [hσ₁]

  have key : ∀ x, Θ x = Λ (Φ (τ x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, hτzero, map_zero, map_zero]
    | tmul a w =>
      obtain ⟨v, rfl⟩ := IsLocalRing.residue_surjective w
      exact (key1 a v).symm
    | add x y hx hy => rw [map_add, hx, hy, hτadd, map_add, map_add]
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · rw [key, key] at hxy
    exact hτbij.1 (hΦinj (Λ.injective hxy))
  · obtain ⟨w, rfl⟩ := hΛsurj z
    letI := Φ.toRingHom.toAlgebra
    haveI := hΦfrac
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := k ⊗[(ResidueField O)] ↥(((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).functionField)) w
    obtain ⟨a', rfl⟩ := hτbij.2 a
    obtain ⟨b', rfl⟩ := hτbij.2 b
    refine ⟨a', b', ?_, ?_⟩
    · rw [key]
      intro h0
      apply nonZeroDivisors.ne_zero hb
      apply hΦinj
      rw [map_zero]
      exact (map_eq_zero Λ).mp h0
    · rw [key, key, map_div₀]
      rfl

end Assembly
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.E87FF"

section Public

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
  (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (toκ : O →+* k)

include hϖ in
set_option maxHeartbeats 3200000 in
theorem injective_and_frac_compInf
    [algk : Algebra O k] (halgk : algebraMap O k = toκ)
    [algK : Algebra O (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C))))]
    (halgK : ∀ a : O, algebraMap O (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)))) a =
      residue _ (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)) trivial).hom
        (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a))))
    (Θ : k ⊗[O] (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)))) →+* ↥((𝔛.ratModel k).C.functionField))
    (hΘk : ∀ a : k, Θ (a ⊗ₜ 1) = AlgebraicCurve.baseToFunctionField (𝔛.ratModel k).toBase a)
    (hΘK : ∀ v : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
      Θ (1 ⊗ₜ residue _ v) = ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).stalkMap (genericPoint ↥(𝔛.ratModel k).C)).hom v)

    (Λpack : haveI : CharP (ResidueField O) p := charP_residueField p O hϖ
      ∀ (i : (ResidueField O) →+* k), i.comp (residue O) = toκ →
      letI : Algebra (ResidueField O) k := i.toAlgebra
      ∃ Λ : ↥((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).functionField) →+* ↥((𝔛.ratModel k).C.functionField),
        Function.Surjective Λ ∧
        (∀ a : k, Λ (AlgebraicCurve.baseToFunctionField
          (pullback.snd ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) a) =
          AlgebraicCurve.baseToFunctionField (𝔛.ratModel k).toBase a) ∧
        (∀ (W : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) (hW : ζ₁ p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) ∈ W) (s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.obj (Opposite.op W))
          [Nonempty (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W : ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).Opens) : Scheme.{0})]
          [Nonempty (((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ⁻¹ᵁ ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W) : ((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).Opens) : Scheme.{0})],
          Λ ((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).germToFunctionField ((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ⁻¹ᵁ ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W)) (((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).app ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W)).hom (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.app W).hom s))) =
            ((𝔛.compInf k ≫ bck p (ResidueField O) k (algebraMap (ResidueField O) k)).stalkMap (genericPoint ↥(𝔛.ratModel k).C)).hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.germ W (ζ₁ p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)) hW).hom s))) :
    Function.Injective Θ ∧ ∀ z : ↥((𝔛.ratModel k).C.functionField), ∃ a b, Θ b ≠ 0 ∧ z = Θ a / Θ b := by
  haveI : CharP (ResidueField O) p := charP_residueField p O hϖ
  haveI : IsLocalHom toκ := isLocalHom_toκ p O hϖ k toκ
  let i : (ResidueField O) →+* k := ResidueField.lift toκ
  have hi : i.comp (residue O) = toκ := ResidueField.lift_comp_residue toκ
  letI algk₀ : Algebra (ResidueField O) k := i.toAlgebra
  obtain ⟨Λ, hΛsurj, hΛ1, hΛ2⟩ := Λpack i hi
  have halgk' : algebraMap O k = (algebraMap (ResidueField O) k).comp (residue O) := by rw [halgk, ← hi]; rfl

  have E : DRModel.baseChangeMap (p := p) toκ = bck p (ResidueField O) k (algebraMap (ResidueField O) k) ≫ bc₀ p O := by
    rw [baseChangeMap_comp_baseChangeMap]
    congr 1
  clear_value i
  revert algK halgK Θ hΘk hΘK
  rw [E]
  intro algK halgK Θ hΘk hΘK
  exact core p 𝔛 O k hϖ halgk' (algK := algK) halgK Θ hΘk hΘK Λ hΛsurj hΛ1 hΛ2

end Public
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.E87FF"

section Lambda

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
  (k : Type) [Field k] [CharP k p] [IsAlgClosed k] [Algebra (ResidueField O) k] [CharP (ResidueField O) p]

theorem V_eq : (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) = ⟨(Set.range (𝔛.compZero k).base)ᶜ,
    (@Scheme.Hom.isClosedEmbedding _ _ (𝔛.compZero k) (𝔛.compZero_isClosedImmersion k)).isClosed_range.isOpen_compl⟩ :=
  TopologicalSpace.Opens.ext (coe_V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k))

scoped instance isOpenImmersion_restrict_compInf_V : IsOpenImmersion ((𝔛.compInf k ⁻¹ᵁ (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens)).ι ≫ 𝔛.compInf k) := by
  rw [V_eq]
  exact ModularCurve.DRModelPackage.isOpenImmersion_restrict_compInf_compl_range_compZero p 𝔛 k

scoped instance nonempty_preimage_V : Nonempty (𝔛.compInf k ⁻¹ᵁ (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : (𝔛.ratModel k).C.Opens) := by
  have hmem := sectionFibre_εinf_mem_V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)
  obtain ⟨c, hc⟩ := 𝔛.εinf_mem_compInf k ⟨IsLocalRing.closedPoint k, rfl⟩
  exact ⟨⟨c, show (𝔛.compInf k).base c ∈ (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) by rw [hc]; exact hmem⟩⟩

def eVU : ((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0}) ≅ (pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) := (isPullback_V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)).isoPullback

theorem eVU_hom_fst : (eVU p 𝔛 O k).hom ≫ (pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) = (bck p (ResidueField O) k (algebraMap (ResidueField O) k)) ∣_ (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)) :=
  (isPullback_V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)).isoPullback_hom_fst

theorem eVU_hom_snd : (eVU p 𝔛 O k).hom ≫ (pullback.snd ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) = (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) :=
  (isPullback_V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)).isoPullback_hom_snd

theorem eVU_hom_fst_ι : (eVU p 𝔛 O k).hom ≫ (pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ≫ (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι = (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens).ι ≫ bck p (ResidueField O) k (algebraMap (ResidueField O) k) := by
  rw [← Category.assoc, eVU_hom_fst, morphismRestrict_ι]

theorem eVU_genericPoint : (eVU p 𝔛 O k).hom.base (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) = (genericPoint ↥(pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))) :=
  genericPoint_eq_of_isOpenImmersion _

def Pfx : ((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).functionField ⟶ ((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0}).functionField :=
  (((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).presheaf.stalkCongr (.of_eq (eVU_genericPoint p 𝔛 O k).symm)).hom ≫
    (eVU p 𝔛 O k).hom.stalkMap (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0}))

scoped instance isIso_Pfx : IsIso (Pfx p 𝔛 O k) := by
  unfold Pfx; exact IsIso.comp_isIso

theorem Pfx_germ {Z : Scheme.{0}} (f : (pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ⟶ Z) (W : Z.Opens) (t : Γ(Z, W))
    (h₁ : f.base (genericPoint ↥(pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))) ∈ W) (h₂ : ((eVU p 𝔛 O k).hom ≫ f).base (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) ∈ W) :
    (Pfx p 𝔛 O k).hom ((((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).presheaf.germ (f ⁻¹ᵁ W) (genericPoint ↥(pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))) h₁).hom ((f.app W).hom t)) =
      (((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0}).presheaf.germ (((eVU p 𝔛 O k).hom ≫ f) ⁻¹ᵁ W) (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) h₂).hom ((((eVU p 𝔛 O k).hom ≫ f).app W).hom t) := by
  have h₁' : (eVU p 𝔛 O k).hom.base (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) ∈ f ⁻¹ᵁ W := h₂
  change ((eVU p 𝔛 O k).hom.stalkMap (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0}))).hom (((((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).presheaf.stalkCongr
    (.of_eq (eVU_genericPoint p 𝔛 O k).symm)).hom).hom ((((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).presheaf.germ (f ⁻¹ᵁ W) (genericPoint ↥(pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))) h₁).hom ((f.app W).hom t))) = _
  rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes_apply]
  erw [Scheme.Hom.germ_stalkMap_apply (eVU p 𝔛 O k).hom (f ⁻¹ᵁ W) (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) h₁']
  rfl

set_option maxHeartbeats 3200000 in

theorem Λpack_compInf :
    ∃ Λ : ↥((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).functionField) →+* ↥((𝔛.ratModel k).C.functionField),
      Function.Surjective Λ ∧
      (∀ a : k, Λ (AlgebraicCurve.baseToFunctionField (pullback.snd ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) a) =
        AlgebraicCurve.baseToFunctionField (𝔛.ratModel k).toBase a) ∧
      (∀ (W : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) (hW : ζ₁ p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) ∈ W) (s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.obj (Opposite.op W))
        [Nonempty (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W : ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens) : Scheme.{0}).Opens) : Scheme.{0})]
        [Nonempty (((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ⁻¹ᵁ ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W) : ((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).Opens) : Scheme.{0})],
        Λ ((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).germToFunctionField ((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ⁻¹ᵁ ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W)) (((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).app ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W)).hom (((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.app W).hom s))) =
          ((𝔛.compInf k ≫ bck p (ResidueField O) k (algebraMap (ResidueField O) k)).stalkMap (genericPoint ↥(𝔛.ratModel k).C)).hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).presheaf.germ W (ζ₁ p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k)) hW).hom s)) := by
  let Λ0 := E87FF.Λ (𝔛.compInf k) (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens)
  refine ⟨(Pfx p 𝔛 O k ≫ Λ0.hom).hom, ?_, ?_, ?_⟩
  · exact (ConcreteCategory.bijective_of_isIso (Pfx p 𝔛 O k ≫ Λ0.hom)).2
  ·
    intro a
    have hV1 : (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens).ι.base (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) ∈ (⊤ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) := trivial
    have hC1 : (𝔛.compInf k).base (genericPoint ↥(𝔛.ratModel k).C) ∈ (⊤ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) := trivial
    change Λ0.hom.hom ((Pfx p 𝔛 O k).hom ((((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).presheaf.germ ⊤ (genericPoint ↥(pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))) trivial).hom
      (((pullback.snd ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)))) = _
    have step1 := Pfx_germ p 𝔛 O k (pullback.snd ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a) trivial trivial
    erw [step1]
    have step2 := E87FF.germ_app_congr (eVU_hom_snd p 𝔛 O k) ⊤ (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) trivial trivial ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a)
    erw [step2]
    have step3 := E87FF.Λ_germ (𝔛.compInf k) (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) ⊤ (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)) hV1 hC1
    erw [step3]

    have step4 := E87FF.germ_app_congr (𝔛.compInf_over k) ⊤ (genericPoint ↥(𝔛.ratModel k).C) trivial trivial ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a)
    simp only [Scheme.Hom.comp_app] at step4
    exact step4
  · intro W hW s _ _
    have hgenU : (pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))).base (genericPoint ↥(pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))) ∈ (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W := by
      change _ ∈ (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ⁻¹ᵁ W; rw [π_genericPoint]
      change (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι.base _ ∈ W; rw [ι_genericPoint_U]; exact hW
    have hζ : (𝔛.compInf k ≫ bck p (ResidueField O) k (algebraMap (ResidueField O) k)).base (genericPoint ↥(𝔛.ratModel k).C) ∈ W := hW
    have hVW : ((eVU p 𝔛 O k).hom ≫ (pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ≫ (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι).base (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) ∈ W := by
      rw [eVU_hom_fst_ι]
      change (bck p (ResidueField O) k (algebraMap (ResidueField O) k)).base ((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens).ι.base (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0}))) ∈ W
      rw [E87FF.ι_genericPoint_eq (𝔛.compInf k) (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens)]
      exact hζ
    change Λ0.hom.hom ((Pfx p 𝔛 O k).hom ((((pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))).presheaf.germ (((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ≫ (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι) ⁻¹ᵁ W) (genericPoint ↥(pullback ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k))))) hgenU).hom
      ((((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ≫ (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι).app W).hom s))) = _
    have step1 := Pfx_germ p 𝔛 O k ((pullback.fst ((U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O)))))) (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField O) k)))) ≫ (U p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ResidueField O))))).Opens).ι) W s hgenU hVW
    erw [step1]
    have hVW' : ((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens).ι ≫ bck p (ResidueField O) k (algebraMap (ResidueField O) k)).base (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) ∈ W := by rw [← eVU_hom_fst_ι]; exact hVW
    have step2 := E87FF.germ_app_congr (eVU_hom_fst_ι p 𝔛 O k) W (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) hVW hVW' s
    erw [step2]
    have hV1 : (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens).ι.base (genericPoint ↥((V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Scheme.{0})) ∈ (bck p (ResidueField O) k (algebraMap (ResidueField O) k)) ⁻¹ᵁ W := hVW'
    have hC1 : (𝔛.compInf k).base (genericPoint ↥(𝔛.ratModel k).C) ∈ (bck p (ResidueField O) k (algebraMap (ResidueField O) k)) ⁻¹ᵁ W := hζ
    have step3 := E87FF.Λ_germ (𝔛.compInf k) (V p 𝔛 (ResidueField O) k (algebraMap (ResidueField O) k) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) ((bck p (ResidueField O) k (algebraMap (ResidueField O) k)) ⁻¹ᵁ W)
      (((bck p (ResidueField O) k (algebraMap (ResidueField O) k)).app W).hom s) hV1 hC1
    erw [step3]

    have step4 := Scheme.Hom.germ_stalkMap_apply (𝔛.compInf k ≫ bck p (ResidueField O) k (algebraMap (ResidueField O) k)) W
      (genericPoint ↥(𝔛.ratModel k).C) hζ s
    erw [step4]
    first
      | rfl
      | (simp only [Scheme.Hom.comp_app]; rfl)

end Lambda
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.E87FF"

section Final

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
  (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (toκ : O →+* k)

include hϖ in

theorem dock_compInf
    [algk : Algebra O k] (halgk : algebraMap O k = toκ)
    [algK : Algebra O (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C))))]
    (halgK : ∀ a : O, algebraMap O (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)))) a =
      residue _ (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)) trivial).hom
        (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a))))
    (Θ : k ⊗[O] (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)))) →+* ↥((𝔛.ratModel k).C.functionField))
    (hΘk : ∀ a : k, Θ (a ⊗ₜ 1) = AlgebraicCurve.baseToFunctionField (𝔛.ratModel k).toBase a)
    (hΘK : ∀ v : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
      Θ (1 ⊗ₜ residue _ v) = ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).stalkMap (genericPoint ↥(𝔛.ratModel k).C)).hom v) :
    Function.Injective Θ ∧ ∀ z : ↥((𝔛.ratModel k).C.functionField), ∃ a b, Θ b ≠ 0 ∧ z = Θ a / Θ b :=
  injective_and_frac_compInf p 𝔛 O hϖ k toκ halgk halgK Θ hΘk hΘK (fun i _ => by
    haveI : CharP (ResidueField O) p := charP_residueField p O hϖ
    letI : Algebra (ResidueField O) k := i.toAlgebra
    exact Λpack_compInf p 𝔛 O k)

end Final
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.E87FF"

end Inf
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.E87FF P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.Dock.Inf"

section Head

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
  (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (toκ : O →+* k)

include hϖ in

theorem injective_and_frac
    (c : (𝔛.ratModel k).C ⟶ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))) (hc : c = 𝔛.compInf k ∨ c = 𝔛.compZero k)
    [algk : Algebra O k] (halgk : algebraMap O k = toκ)
    [algK : Algebra O (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((c ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C))))]
    (halgK : ∀ a : O, algebraMap O (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((c ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)))) a =
      residue _ (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ ((c ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)) trivial).hom
        (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a))))
    (Θ : k ⊗[O] (ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((c ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)))) →+* ↥((𝔛.ratModel k).C.functionField))
    (hΘk : ∀ a : k, Θ (a ⊗ₜ 1) = AlgebraicCurve.baseToFunctionField (𝔛.ratModel k).toBase a)
    (hΘK : ∀ v : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((c ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
      Θ (1 ⊗ₜ residue _ v) = ((c ≫ DRModel.baseChangeMap toκ).stalkMap (genericPoint ↥(𝔛.ratModel k).C)).hom v) :
    Function.Injective Θ ∧ ∀ z : ↥((𝔛.ratModel k).C.functionField), ∃ a b, Θ b ≠ 0 ∧ z = Θ a / Θ b := by
  rcases hc with rfl | rfl
  · exact Inf.dock_compInf p 𝔛 O hϖ k toκ halgk (algK := algK) halgK Θ hΘk hΘK
  · exact dock_compZero p 𝔛 O hϖ k toκ halgk (algK := algK) halgK Θ hΘk hΘK

end Head
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.E87FF P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.Dock.Inf"

end Dock
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.E87FF P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.Dock.Inf P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.Dock"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.E87FF P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.Dock.Inf P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.Dock"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open scoped TensorProduct

theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    {k : Type} [Field k] [CharP k p] [IsAlgClosed k] (toκ : O →+* k)
    (ψ : IsLocalRing.ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
        ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C))) →+* ↥(modularFunctionFieldC k 1))

    (hψO : ∀ a : O, ψ (IsLocalRing.residue _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤
            ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)) trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap k ↥(modularFunctionFieldC k 1) (toκ a))

    (hψ : ∃ v, ψ v ∉ Set.range (algebraMap k ↥(modularFunctionFieldC k 1))) :
    ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D)
      (ιk : k →+* D)
      (ικ : IsLocalRing.ResidueField ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
        ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C))) →+* D)
      (Θ : D →+* (𝔛.ratModel k).C.functionField) (Ψ : D →+* ↥(modularFunctionFieldC k 1)),

      (∀ a : k, Θ (ιk a) = AlgebraicCurve.baseToFunctionField (𝔛.ratModel k).toBase a) ∧
      (∀ v, Θ (ικ v) = IsLocalRing.ResidueField.lift
        (((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).stalkMap (genericPoint ↥(𝔛.ratModel k).C)).hom) v) ∧

      (∀ a : k, Ψ (ιk a) = algebraMap k ↥(modularFunctionFieldC k 1) a) ∧
      (∀ v, Ψ (ικ v) = ψ v) ∧

      Function.Injective Θ ∧
      (∀ z : (𝔛.ratModel k).C.functionField, ∃ a b : D, Θ b ≠ 0 ∧ z = Θ a / Θ b) ∧
      Function.Injective Ψ := by
  classical

  let X : Scheme := pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))
  let M := 𝔛.ratModel k
  let f₂ : M.C ⟶ X := 𝔛.compZero k ≫ DRModel.baseChangeMap toκ
  let η : M.C := genericPoint ↥M.C
  let ξ₂ : X := f₂.base η
  let K : Type := IsLocalRing.ResidueField (X.presheaf.stalk ξ₂)
  let E : Type := ↥(modularFunctionFieldC k 1)
  let F : Type := M.C.functionField

  let e : K →+* F := IsLocalRing.ResidueField.lift ((f₂.stalkMap η).hom)
  let cO : O →+* K := (IsLocalRing.residue (X.presheaf.stalk ξ₂)).comp
    (((X.presheaf.germ ⊤ ξ₂ trivial).hom).comp
      (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom))
  let cF : k →+* F := AlgebraicCurve.baseToFunctionField M.toBase

  letI : Algebra O k := toκ.toAlgebra
  letI : Algebra O K := cO.toAlgebra
  letI algF : Algebra k F := cF.toAlgebra
  letI : Algebra O F := (cF.comp toκ).toAlgebra
  haveI : IsScalarTower O k F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra O E := ((algebraMap k E).comp toκ).toAlgebra
  haveI : IsScalarTower O k E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have he : ∀ a : O, e (cO a) = cF (toκ a) := by
    intro a

    have hsq : f₂ ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
        M.toBase ≫ Spec.map (CommRingCat.ofHom toκ) := by
      simp only [f₂, M, Category.assoc, DRModel.baseChangeMap, pullback.lift_snd]
      rw [← Category.assoc, 𝔛.compZero_over k]
    simp only [e, cO, RingHom.comp_apply, IsLocalRing.ResidueField.lift_residue_apply]
    change ((X.presheaf.germ ⊤ ξ₂ trivial ≫ f₂.stalkMap η).hom)
        (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)) = _
    rw [Scheme.Hom.germ_stalkMap f₂ ⊤ η trivial]
    change (M.C.presheaf.germ ⊤ η trivial).hom ((f₂.appTop).hom
        (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a))) = _
    rw [← CommRingCat.comp_apply _ f₂.appTop, ← Scheme.Hom.comp_appTop, hsq, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      ← CommRingCat.comp_apply _ (Spec.map (CommRingCat.ofHom toκ)).appTop, ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply]
    rfl
  have hψ' : ∀ a : O, ψ (cO a) = algebraMap k E (toκ a) := hψO
  let eO : K →ₐ[O] F := { e with commutes' := fun a => he a }
  let ψO : K →ₐ[O] E := { ψ with commutes' := fun a => hψ' a }

  let D : Type := k ⊗[O] K
  let Θ : D →ₐ[k] F := Algebra.TensorProduct.lift (Algebra.ofId k F) eO (fun _ _ => Commute.all _ _)
  let Ψ : D →ₐ[k] E := Algebra.TensorProduct.lift (Algebra.ofId k E) ψO (fun _ _ => Commute.all _ _)
  have hΘk : ∀ a : k, Θ (a ⊗ₜ (1 : K)) = cF a := by
    intro a
    simp only [Θ]
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, mul_one, Algebra.ofId_apply]
    rfl
  have hΘκ : ∀ v : K, Θ ((1 : k) ⊗ₜ v) = e v := by
    intro v
    simp only [Θ]
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl
  have hΨk : ∀ a : k, Ψ (a ⊗ₜ (1 : K)) = algebraMap k E a := by
    intro a
    simp only [Ψ]
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, mul_one, Algebra.ofId_apply]
  have hΨκ : ∀ v : K, Ψ ((1 : k) ⊗ₜ v) = ψ v := by
    intro v
    simp only [Ψ]
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl

  have hΘ : Function.Injective Θ ∧ ∀ z : F, ∃ a b : D, Θ b ≠ 0 ∧ z = Θ a / Θ b := by
    have hmain := Dock.injective_and_frac p 𝔛 O hϖ k toκ (𝔛.compZero k) (Or.inr rfl) rfl (fun a => rfl) Θ.toRingHom
      (fun a => hΘk a)
      (fun v => (hΘκ (IsLocalRing.residue _ v)).trans (IsLocalRing.ResidueField.lift_residue_apply _ v))
    exact hmain
  haveI : IsDomain D := Function.Injective.isDomain Θ.toRingHom hΘ.1

  have hL : Algebra.trdeg k F ≤ 1 := by
    rw [← (M.ffAlgEquiv).trdeg_eq]
    exact (RatFunc.trdeg_eq_one k).le

  have hΨ : Function.Injective Ψ := by
    obtain ⟨v, hv⟩ := hψ
    refine AlgHom.injective_of_trdeg_le_one_of_exists_transcendental Θ hΘ.1 hL Ψ ⟨(1 : k) ⊗ₜ v, ?_⟩
    rw [hΨκ]

    intro halg
    exact hv (minpoly.mem_range_of_degree_eq_one k _
      (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible halg.isIntegral)))

  refine ⟨D, inferInstance, inferInstance, Algebra.TensorProduct.includeLeftRingHom,
    (Algebra.TensorProduct.includeRight (R := O) (A := k) (B := K)).toRingHom, Θ.toRingHom, Ψ.toRingHom,
    ?_, ?_, ?_, ?_, hΘ.1, hΘ.2, hΨ⟩
  · intro a; exact hΘk a
  · intro v; exact hΘκ v
  · intro a; exact hΨk a
  · intro v; exact hΨκ v

end S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero (solution)
