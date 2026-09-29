-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mul_eq_of_mem_fieldOver_nodeIntegersOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/aa97a97e-9715-5e93-8713-e05ea760db22

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_isIntegral_jqNModC_all
import Theorems.Thm_ModularCurve_exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_fieldOver_nodeIntegersOver
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong"
p2m_attr_erase "simp" "NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

open ModularCurve ModularCurve.NodeLocalized

namespace NodeNormalization
noncomputable section

private theorem jRing_le_fieldOver (M : ℕ) [NeZero M] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    (jRing A K : Set (LaurentSeries (AlgebraicClosure ℚ))) ⊆ fieldOver M K := by
  change jRing A K ≤ (fieldOver M K).toSubring
  rw [jRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | hx)
  · exact Subfield.subset_closure (Or.inl ⟨⟨(a : AlgebraicClosure ℚ), (Subring.mem_inf.1 a.2).2⟩, rfl⟩)
  · rw [Set.mem_singleton_iff] at hx
    exact Subfield.subset_closure (Or.inr (Or.inl hx))
section Tower

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

private def jField : Subfield (LaurentSeries (AlgebraicClosure ℚ)) :=
  Subfield.closure (jRing A K : Set (LaurentSeries (AlgebraicClosure ℚ)))

private theorem jRing_le_jField : (jRing A K : Set (LaurentSeries (AlgebraicClosure ℚ))) ⊆ jField A K :=
  Subfield.subset_closure

private theorem jField_le_fieldOver (M : ℕ) [NeZero M] : jField A K ≤ fieldOver M K :=
  Subfield.closure_le.2 (jRing_le_fieldOver M A K)

private theorem jqModC_mem_jRing : jqModC (AlgebraicClosure ℚ) ∈ jRing A K :=
  Subring.subset_closure (Or.inr rfl)

private theorem constSeries_mem_jRing (a : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) a ∈ jRing A K :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

private theorem jqNModC_mem_fieldOver (M : ℕ) [NeZero M] :
    jqNModC (AlgebraicClosure ℚ) M ∈ fieldOver M K :=
  Subfield.subset_closure (Or.inr (Or.inr rfl))

private noncomputable def jRingToJField : ↥(jRing A K) →+* ↥(jField A K) :=
  (jRing A K).subtype.codRestrict (jField A K) fun x => jRing_le_jField A K x.2

private noncomputable def jRingToFieldOver (M : ℕ) [NeZero M] : ↥(jRing A K) →+* ↥(fieldOver M K) :=
  (jRing A K).subtype.codRestrict (fieldOver M K) fun x => jRing_le_fieldOver M A K x.2

private noncomputable scoped instance algebraJRingJField : Algebra ↥(jRing A K) ↥(jField A K) :=
  (jRingToJField A K).toAlgebra

private noncomputable scoped instance algebraJFieldFieldOver (M : ℕ) [NeZero M] :
    Algebra ↥(jField A K) ↥(fieldOver M K) :=
  (Subfield.inclusion (jField_le_fieldOver A K M)).toAlgebra

private noncomputable scoped instance algebraJRingFieldOver (M : ℕ) [NeZero M] :
    Algebra ↥(jRing A K) ↥(fieldOver M K) :=
  (jRingToFieldOver A K M).toAlgebra

private theorem coe_algebraMap_jRing_jField (x : ↥(jRing A K)) :
    ((algebraMap ↥(jRing A K) ↥(jField A K) x : ↥(jField A K)) : LaurentSeries (AlgebraicClosure ℚ))
      = x := by
  rw [RingHom.algebraMap_toAlgebra]
  exact RingHom.codRestrict_apply _ _ _ _

private theorem coe_algebraMap_jField_fieldOver (M : ℕ) [NeZero M] (x : ↥(jField A K)) :
    ((algebraMap ↥(jField A K) ↥(fieldOver M K) x : ↥(fieldOver M K)) :
      LaurentSeries (AlgebraicClosure ℚ)) = x := by
  rw [RingHom.algebraMap_toAlgebra]
  exact RingHom.codRestrict_apply _ _ _ _

private scoped instance isScalarTower_jRing_jField_fieldOver (M : ℕ) [NeZero M] :
    IsScalarTower ↥(jRing A K) ↥(jField A K) ↥(fieldOver M K) := by
  refine IsScalarTower.of_algebraMap_eq fun x => Subtype.ext ?_
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
  rw [jRingToFieldOver, RingHom.codRestrict_apply, Subfield.inclusion, RingHom.codRestrict_apply,
    Subfield.coe_subtype, jRingToJField, RingHom.codRestrict_apply]

private scoped instance isScalarTower_jRing_fieldOver_laurent (M : ℕ) [NeZero M] :
    IsScalarTower ↥(jRing A K) ↥(fieldOver M K) (LaurentSeries (AlgebraicClosure ℚ)) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private scoped instance isFractionRing_jRing : IsFractionRing ↥(jRing A K) ↥(jField A K) := by
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · intro y
    refine IsUnit.mk0 _ fun h => nonZeroDivisors.ne_zero y.2 ?_
    have h' := congrArg Subtype.val h
    rw [coe_algebraMap_jRing_jField, ZeroMemClass.coe_zero] at h'
    exact Subtype.ext h'
  · rintro ⟨z, hz⟩
    obtain ⟨y, hy, w, hw, rfl⟩ := Subfield.mem_closure_iff.1 hz
    rw [Subring.closure_eq] at hy hw
    by_cases hw0 : w = 0
    · refine ⟨(0, 1), Subtype.ext ?_⟩
      subst hw0
      rw [MulMemClass.coe_mul, coe_algebraMap_jRing_jField, coe_algebraMap_jRing_jField,
        ZeroMemClass.coe_zero]
      show y / 0 * _ = 0
      rw [div_zero, zero_mul]
    · refine ⟨(⟨y, hy⟩, ⟨⟨w, hw⟩, mem_nonZeroDivisors_of_ne_zero fun h => hw0 ?_⟩), Subtype.ext ?_⟩
      · exact congrArg Subtype.val h
      · rw [MulMemClass.coe_mul, coe_algebraMap_jRing_jField, coe_algebraMap_jRing_jField]
        show y / w * w = y
        exact div_mul_cancel₀ y hw0
  · intro x y h
    have h' := congrArg Subtype.val h
    rw [coe_algebraMap_jRing_jField, coe_algebraMap_jRing_jField] at h'
    exact ⟨1, by rw [Subtype.ext h']⟩

private theorem adjoin_jqNModC_eq_top (M : ℕ) [NeZero M] :
    IntermediateField.adjoin ↥(jField A K)
      {(⟨jqNModC (AlgebraicClosure ℚ) M, jqNModC_mem_fieldOver K M⟩ : ↥(fieldOver M K))} = ⊤ := by
  set T := IntermediateField.adjoin ↥(jField A K)
      {(⟨jqNModC (AlgebraicClosure ℚ) M, jqNModC_mem_fieldOver K M⟩ : ↥(fieldOver M K))} with hT
  have key : fieldOver M K ≤ T.toSubfield.map (fieldOver M K).subtype := by
    conv_lhs => rw [fieldOver]
    rw [Subfield.closure_le]
    rintro g (⟨c, rfl⟩ | hg)
    · rcases A.mem_or_inv_mem (c : AlgebraicClosure ℚ) with hc | hc
      · refine ⟨algebraMap (jField A K) (fieldOver M K)
          ⟨_, jRing_le_jField A K (constSeries_mem_jRing A K ⟨c, Subring.mem_inf.2 ⟨hc, c.2⟩⟩)⟩,
          T.algebraMap_mem _, ?_⟩
        rw [Subfield.coe_subtype, coe_algebraMap_jField_fieldOver]
        rfl
      · by_cases hc0 : (c : AlgebraicClosure ℚ) = 0
        · refine ⟨0, (zero_mem T.toSubfield : (0 : ↥(fieldOver M K)) ∈ T.toSubfield), ?_⟩
          rw [map_zero]
          show (0 : LaurentSeries (AlgebraicClosure ℚ))
            = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ)
          rw [hc0, map_zero]
        · have hcK : (c : AlgebraicClosure ℚ)⁻¹ ∈ K.toSubalgebra.toSubring :=
            (inv_mem (show (c : AlgebraicClosure ℚ) ∈ K from c.2) : (c : AlgebraicClosure ℚ)⁻¹ ∈ K)
          refine ⟨(algebraMap (jField A K) (fieldOver M K)
            ⟨_, jRing_le_jField A K (constSeries_mem_jRing A K ⟨_, Subring.mem_inf.2 ⟨hc, hcK⟩⟩)⟩)⁻¹,
            inv_mem (T.algebraMap_mem _), ?_⟩
          rw [map_inv₀, Subfield.coe_subtype, coe_algebraMap_jField_fieldOver]
          show (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))
              (c : AlgebraicClosure ℚ)⁻¹)⁻¹
            = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ)
          rw [map_inv₀, inv_inv]
    · rcases hg with rfl | rfl
      · refine ⟨algebraMap (jField A K) (fieldOver M K) ⟨_, jRing_le_jField A K (jqModC_mem_jRing A K)⟩,
          T.algebraMap_mem _, ?_⟩
        rw [Subfield.coe_subtype, coe_algebraMap_jField_fieldOver]
      · exact ⟨_, IntermediateField.mem_adjoin_simple_self _ _, rfl⟩
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  obtain ⟨y, hy, hyx⟩ := key hx
  have : y = ⟨x, hx⟩ := Subtype.ext hyx
  exact this ▸ hy

end Tower
section Finite

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

private theorem adjoin_rat_jqModC_le_comap :
    (IntermediateField.adjoin ℚ ({jqModC ℚ} : Set (LaurentSeries ℚ))).toSubfield
      ≤ (jField A K).comap (coeffEmb (AlgebraicClosure ℚ)) := by
  rw [show (IntermediateField.adjoin ℚ ({jqModC ℚ} : Set (LaurentSeries ℚ))).toSubfield
      = Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ {jqModC ℚ}) from rfl,
    Subfield.closure_le]
  rintro x (⟨r, rfl⟩ | hx)
  · show coeffEmb (AlgebraicClosure ℚ) (algebraMap ℚ (LaurentSeries ℚ) r) ∈ jField A K
    rw [eq_ratCast, map_ratCast]
    exact SubfieldClass.ratCast_mem _ r
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    show coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) ∈ jField A K
    rw [coeffEmb, coeffSemilinearAut.coeffMap_jqModC]
    exact jRing_le_jField A K (jqModC_mem_jRing A K)

private noncomputable def ratJFieldToJField :
    ↥(IntermediateField.adjoin ℚ ({jqModC ℚ} : Set (LaurentSeries ℚ))) →+* ↥(jField A K) :=
  ((coeffEmb (AlgebraicClosure ℚ)).comp
      (algebraMap ↥(IntermediateField.adjoin ℚ ({jqModC ℚ} : Set (LaurentSeries ℚ)))
        (LaurentSeries ℚ))).codRestrict
    (jField A K) fun x => adjoin_rat_jqModC_le_comap A K x.2

private theorem isIntegral_jqNModC (M : ℕ) [NeZero M] :
    IsIntegral ↥(jField A K)
      (⟨jqNModC (AlgebraicClosure ℚ) M, jqNModC_mem_fieldOver K M⟩ : ↥(fieldOver M K)) := by
  obtain ⟨P, hPm, hP0⟩ := isIntegral_jqNModC_all ℚ M
  refine ⟨P.map (ratJFieldToJField A K), hPm.map _, Subtype.ext ?_⟩
  have h := congrArg (coeffEmb (AlgebraicClosure ℚ)) hP0
  rw [Polynomial.hom_eval₂, map_zero,
    show coeffEmb (AlgebraicClosure ℚ) (jqNModC ℚ M) = jqNModC (AlgebraicClosure ℚ) M by
      rw [coeffEmb, coeffSemilinearAut.coeffMap_jqNModC]] at h
  have hcomp : (fieldOver M K).subtype.comp
      ((algebraMap ↥(jField A K) ↥(fieldOver M K)).comp (ratJFieldToJField A K))
      = (coeffEmb (AlgebraicClosure ℚ)).comp (algebraMap _ (LaurentSeries ℚ)) := by
    refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, Subfield.coe_subtype, coe_algebraMap_jField_fieldOver,
      ratJFieldToJField, RingHom.codRestrict_apply]
  rw [Polynomial.eval₂_map, ZeroMemClass.coe_zero, ← Subfield.coe_subtype, Polynomial.hom_eval₂, hcomp]
  exact h

private scoped instance finiteDimensional_fieldOver (M : ℕ) [NeZero M] :
    FiniteDimensional ↥(jField A K) ↥(fieldOver M K) := by
  haveI := IntermediateField.adjoin.finiteDimensional (isIntegral_jqNModC A K M)
  refine Module.Finite.of_surjective
    (IntermediateField.adjoin ↥(jField A K)
      {(⟨jqNModC (AlgebraicClosure ℚ) M, jqNModC_mem_fieldOver K M⟩ :
        ↥(fieldOver M K))}).val.toLinearMap fun x => ?_
  refine ⟨⟨x, ?_⟩, rfl⟩
  rw [adjoin_jqNModC_eq_top]
  exact IntermediateField.mem_top

end Finite
section HeightOne

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
  (M : ℕ) [NeZero M]

private theorem jRing_le_jIntegralClosure : jRing A K ≤ jIntegralClosure M A K := fun x hx =>
  ⟨jRing_le_fieldOver M A K hx, isIntegral_algebraMap (R := ↥(jRing A K)) (x := ⟨x, hx⟩)⟩

end HeightOne

end
section Vertical

open AlgebraicCurve

variable {L₀ : Type*} [Field L₀] {A₀ : ValuationSubring L₀} {E : Type*} [Field E] [Algebra L₀ E]
  {Fb Fb' : Type*} [Field Fb] [Field Fb'] [Algebra (IsLocalRing.ResidueField A₀) Fb]
  [Algebra (IsLocalRing.ResidueField A₀) Fb']

private theorem regularProlongation_integers_eq_of_le (S : RegularProlongation A₀ E Fb)
    (S' : RegularProlongation A₀ E Fb') (h : S.integers ≤ S'.integers) :
    S.integers = S'.integers := by
  refine le_antisymm h ?_
  intro f hf'
  by_cases hf0 : f = 0
  · rw [hf0]; exact zero_mem _
  obtain ⟨c, hc, hres⟩ := S.exists_smul_mem f hf0
  have hc0 : c ≠ 0 := S.smul_const_ne_zero hc hres
  have hu : IsUnit (⟨c • f, hc⟩ : S.integers) := S.isUnit_of_residue_ne_zero hres
  have h1 : ((↑(hu.unit⁻¹) : S.integers) : E) * (c • f) = 1 := by
    have h2 : ((hu.unit⁻¹ : S.integersˣ) : S.integers) * (hu.unit : S.integers) = 1 :=
      hu.unit.inv_val
    rw [IsUnit.unit_spec] at h2
    exact congrArg Subtype.val h2
  have hinvS : (c • f)⁻¹ ∈ S.integers := by
    rw [← eq_inv_of_mul_eq_one_left h1]; exact (↑(hu.unit⁻¹) : S.integers).2
  have hsmul : c • f = algebraMap L₀ E c * f := Algebra.smul_def c f
  have hcinv : algebraMap L₀ E c⁻¹ = f * (c • f)⁻¹ := by
    rw [map_inv₀, hsmul, mul_inv, mul_left_comm, mul_inv_cancel₀ hf0, mul_one]
  have hmemS' : algebraMap L₀ E c⁻¹ ∈ S'.integers := by
    rw [hcinv]; exact mul_mem hf' (h hinvS)
  have hcA : c⁻¹ ∈ A₀ := (S'.algebraMap_mem_iff c⁻¹).mp hmemS'
  have hmemS : algebraMap L₀ E c⁻¹ ∈ S.integers := (S.algebraMap_mem_iff c⁻¹).mpr hcA
  have hf_eq : f = algebraMap L₀ E c⁻¹ * (c • f) := by
    rw [hsmul, map_inv₀, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero _).mpr hc0), one_mul]
  rw [hf_eq]; exact mul_mem hmemS hc

private theorem liesOverPrime_of_red {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] (red₀ : A →+* k) : A.LiesOverPrime q := by
  have hq : ((q : A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := map_natCast A.subtype q
  show (q : AlgebraicClosure ℚ) ∈ A.nonunits
  rw [← hq, ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h := hu.map red₀
  rw [map_natCast, CharP.cast_eq_zero] at h
  exact not_isUnit_zero h

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem maximalIdeal_le_ker_red (R : PlaceSpecialization.ProlongationTuple P) :
    IsLocalRing.maximalIdeal A ≤ RingHom.ker red := by
  intro a ha
  rw [RingHom.mem_ker, ← R.redBar_residue a, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero]

private def packA {z : LaurentSeries (AlgebraicClosure ℚ)}
    (hz : z ∈ CharPReduction.integralCoeffs A.toSubring) : LaurentSeries A where
  coeff n := ⟨z.coeff n, hz n⟩
  isPWO_support' := z.isPWO_support.mono (fun _ hn h => hn (Subtype.ext h))

private theorem coeffMap_subtype_packA {z : LaurentSeries (AlgebraicClosure ℚ)}
    (hz : z ∈ CharPReduction.integralCoeffs A.toSubring) :
    coeffMap A.subtype (packA hz) = z := by
  ext n
  rfl

set_option synthInstance.maxHeartbeats 1600000 in

private theorem integersFst_le (R : PlaceSpecialization.ProlongationTuple P)
    (S : RegularProlongation A (modularFunctionFieldBar (N * q))
      (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N))
    (hS : ∀ f : modularFunctionFieldBar (N * q), f ∈ S.integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) :
    R.R₁.integers ≤ S.integers := by
  intro f hf
  rw [hS]
  have hf' := (R.mem_integersFst_iff f).mp hf
  obtain ⟨r, s, hs, hfs⟩ := (CharPReduction.mem_localizedAtKer A.toSubring red _ _).mp hf'
  have hrI := CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring r.2
  have hsI := CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring s.2
  refine ⟨packA hrI, packA hsI, ?_, ?_⟩
  · intro h0
    apply (CharPReduction.notMem_redKer_iff A.toSubring red _ _).mp hs
    ext n
    rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff]
    have hn : IsLocalRing.residue A ⟨(s : LaurentSeries (AlgebraicClosure ℚ)).coeff n, hsI n⟩ = 0 :=
      congrArg (fun z : LaurentSeries (IsLocalRing.ResidueField A) => z.coeff n) h0
    have hmem := maximalIdeal_le_ker_red R ((IsLocalRing.residue_eq_zero_iff _).mp hn)
    exact RingHom.mem_ker.mp hmem
  · rw [coeffMap_subtype_packA, coeffMap_subtype_packA]
    exact hfs

set_option synthInstance.maxHeartbeats 1600000 in

private theorem integersSnd_le (R : PlaceSpecialization.ProlongationTuple P)
    (S₀ S₁ : RegularProlongation A (modularFunctionFieldBar (N * q))
      (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N))
    (hS₀ : ∀ f : modularFunctionFieldBar (N * q), f ∈ S₀.integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hS₁ : ∀ f : modularFunctionFieldBar (N * q), f ∈ S₁.integers ↔
      geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q))
        (atkinLehnerInvolutionFull N q) f ∈ S₀.integers) :
    R.R₂.integers ≤ S₁.integers := by
  intro f hf
  rw [hS₁]
  exact integersFst_le R S₀ hS₀ ((R.mem_integers₂_iff f).mp hf)

set_option synthInstance.maxHeartbeats 1600000 in

private theorem integers_eq_and_eq (R : PlaceSpecialization.ProlongationTuple P)
    (S₀ S₁ : RegularProlongation A (modularFunctionFieldBar (N * q))
      (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N))
    (hS₀ : ∀ f : modularFunctionFieldBar (N * q), f ∈ S₀.integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hS₁ : ∀ f : modularFunctionFieldBar (N * q), f ∈ S₁.integers ↔
      geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q))
        (atkinLehnerInvolutionFull N q) f ∈ S₀.integers) :
    R.R₁.integers = S₀.integers ∧ R.R₂.integers = S₁.integers :=
  ⟨regularProlongation_integers_eq_of_le R.R₁ S₀ (integersFst_le R S₀ hS₀),
    regularProlongation_integers_eq_of_le R.R₂ S₁ (integersSnd_le R S₀ S₁ hS₀ hS₁)⟩

end Vertical
section Seam

private theorem fieldOver_le_modularFunctionFieldBar (M : ℕ) [NeZero M]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    fieldOver M K ≤ (modularFunctionFieldBar M).toSubfield := by
  refine Subfield.closure_le.mpr ?_
  rintro x (⟨a, rfl⟩ | hx)
  · exact (modularFunctionFieldBar M).algebraMap_mem (a : AlgebraicClosure ℚ)
  · rcases hx with rfl | rfl
    · have h : jqModC (AlgebraicClosure ℚ) = coeffEmb (AlgebraicClosure ℚ) jq := by
        rw [← jqModC_rat, coeffEmb, coeffMap_jqModC]
      rw [h]
      exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full M (jq_mem M))
    · have h : jqNModC (AlgebraicClosure ℚ) M = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M jq) := by
        rw [← jqModC_rat, coeffEmb, coeffMap_qExpand, coeffMap_jqModC]
        rfl
      rw [h]
      exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full M (jqN_mem M))

end Seam
section NodePrime

private theorem jRing_le_modularLocalized (M : ℕ) [NeZero M] (A : ValuationSubring (AlgebraicClosure ℚ))
    {k : Type*} [Field k] (red : ↥A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    jRing A K ≤ CharPReduction.modularLocalized M A.toSubring red := by
  have h : CharPReduction.modularRing M A.toSubring
      ≤ CharPReduction.modularLocalized M A.toSubring red :=
    CharPReduction.subring_le_localizedAtKer _ _ _ _
  refine le_trans (Subring.closure_le.mpr ?_) h
  rintro x (⟨b, rfl⟩ | rfl)
  · exact CharPReduction.constSeries_mem_modularRing M A.toSubring
      ⟨b, (Subring.mem_inf.mp b.2).1⟩
  · exact CharPReduction.jqModC_mem_modularRing M A.toSubring

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

set_option synthInstance.maxHeartbeats 1600000 in

private theorem mem_integersFst_of_mem_jIntegralClosure (R : PlaceSpecialization.ProlongationTuple P)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (c : ↥(jIntegralClosure (N * q) A K)) :
    (⟨(c : LaurentSeries (AlgebraicClosure ℚ)),
        fieldOver_le_modularFunctionFieldBar (N * q) K c.2.1⟩ : modularFunctionFieldBar (N * q))
      ∈ R.R₁.integers := by

  have hB : ∀ x : ↥(jRing A K),
      (x : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (N * q) := fun x =>
    fieldOver_le_modularFunctionFieldBar (N * q) K (jRing_le_fieldOver (N * q) A K x.2)
  have hW : ∀ x : ↥(jRing A K), (⟨(x : LaurentSeries (AlgebraicClosure ℚ)), hB x⟩ :
      modularFunctionFieldBar (N * q)) ∈ R.R₁.integers := fun x =>
    (R.mem_integersFst_iff _).mpr (jRing_le_modularLocalized (N * q) A red K x.2)
  let ψ : ↥(jRing A K) →+* ↥R.R₁.integers :=
    ((jRing A K).subtype.codRestrict (modularFunctionFieldBar (N * q)) hB).codRestrict
      R.R₁.integers hW
  have hψ : (algebraMap ↥(modularFunctionFieldBar (N * q)) (LaurentSeries (AlgebraicClosure ℚ))).comp
      ((algebraMap ↥R.R₁.integers ↥(modularFunctionFieldBar (N * q))).comp ψ)
        = algebraMap ↥(jRing A K) (LaurentSeries (AlgebraicClosure ℚ)) :=
    RingHom.ext fun x => rfl

  obtain ⟨p, hp, hpc⟩ := c.2.2
  have hint : IsIntegral ↥R.R₁.integers ((⟨(c : LaurentSeries (AlgebraicClosure ℚ)),
      fieldOver_le_modularFunctionFieldBar (N * q) K c.2.1⟩ : modularFunctionFieldBar (N * q))) := by
    refine ⟨p.map ψ, hp.map ψ, ?_⟩
    rw [Polynomial.eval₂_map]
    apply (algebraMap ↥(modularFunctionFieldBar (N * q)) (LaurentSeries (AlgebraicClosure ℚ))).injective
    rw [Polynomial.hom_eval₂, hψ, map_zero]
    exact hpc
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  rw [← hy]
  exact y.2

end NodePrime
end NodeNormalization
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_fieldOver_nodeIntegersOver.NodeNormalization"

namespace NodeNormalization

section NodeRing

open AlgebraicCurve

private theorem mem_valuationSubring_of_jRing_le (M : ℕ) [NeZero M]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (W : ValuationSubring ↥(modularFunctionFieldBar M))
    (hW : ∀ (x : LaurentSeries (AlgebraicClosure ℚ)) (hx : x ∈ jRing A K),
      (⟨x, fieldOver_le_modularFunctionFieldBar M K (jRing_le_fieldOver M A K hx)⟩ :
        modularFunctionFieldBar M) ∈ W)
    (c : ↥(jIntegralClosure M A K)) :
    (⟨(c : LaurentSeries (AlgebraicClosure ℚ)),
        fieldOver_le_modularFunctionFieldBar M K c.2.1⟩ : modularFunctionFieldBar M) ∈ W := by

  have hB : ∀ x : ↥(jRing A K),
      (x : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar M := fun x =>
    fieldOver_le_modularFunctionFieldBar M K (jRing_le_fieldOver M A K x.2)
  let ψ : ↥(jRing A K) →+* ↥W :=
    ((jRing A K).subtype.codRestrict (modularFunctionFieldBar M) hB).codRestrict W
      fun x => hW x x.2
  have hψ : (algebraMap ↥(modularFunctionFieldBar M) (LaurentSeries (AlgebraicClosure ℚ))).comp
      ((algebraMap ↥W ↥(modularFunctionFieldBar M)).comp ψ)
        = algebraMap ↥(jRing A K) (LaurentSeries (AlgebraicClosure ℚ)) :=
    RingHom.ext fun x => rfl

  obtain ⟨p, hp, hpc⟩ := c.2.2
  have hint : IsIntegral ↥W ((⟨(c : LaurentSeries (AlgebraicClosure ℚ)),
      fieldOver_le_modularFunctionFieldBar M K c.2.1⟩ : modularFunctionFieldBar M)) := by
    refine ⟨p.map ψ, hp.map ψ, ?_⟩
    rw [Polynomial.eval₂_map]
    apply (algebraMap ↥(modularFunctionFieldBar M) (LaurentSeries (AlgebraicClosure ℚ))).injective
    rw [Polynomial.hom_eval₂, hψ, map_zero]
    exact hpc
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  rw [← hy]
  exact y.2

private theorem mem_valuationSubring_of_mem_jRing (M : ℕ) [NeZero M]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (W : ValuationSubring ↥(modularFunctionFieldBar M))
    (hA : ∀ a : AlgebraicClosure ℚ, a ∈ A →
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M) a ∈ W)
    {t : ↥(modularFunctionFieldBar M)} (ht : t ∈ W)
    (htj : (t : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (x : LaurentSeries (AlgebraicClosure ℚ)) (hx : x ∈ jRing A K) :
    (⟨x, fieldOver_le_modularFunctionFieldBar M K (jRing_le_fieldOver M A K hx)⟩ :
      modularFunctionFieldBar M) ∈ W := by
  have hle : jRing A K ≤ W.toSubring.map
      (algebraMap ↥(modularFunctionFieldBar M) (LaurentSeries (AlgebraicClosure ℚ))) := by
    rw [jRing, Subring.closure_le]
    rintro y (⟨a, rfl⟩ | hy)
    · exact ⟨_, hA a (Subring.mem_inf.mp a.2).1, rfl⟩
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨t, ht, htj⟩
  obtain ⟨y, hy, hyx⟩ := Subring.mem_map.mp (hle hx)
  have h : (⟨x, fieldOver_le_modularFunctionFieldBar M K (jRing_le_fieldOver M A K hx)⟩ :
      modularFunctionFieldBar M) = y := Subtype.ext hyx.symm
  rw [h]
  exact hy

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem jFun_mem_toValuationSubring
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hV : jGeomGen k N ∈ (P.reduceFst V).toValuationSubring) :
    PlaceSpecialization.ProlongationTuple.jFun N q ∈ V.toValuationSubring := by

  have h₁ : ¬ ∀ a : ↥A, (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord
      ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
          ≤ 0 :=
    fun hle => not_lt.mpr ((P.reduceFst V).ord_nonneg_of_mem hV) (P.d0_j_pole _ hle)
  push Not at h₁
  obtain ⟨a, ha⟩ := h₁

  have he : 0 < V.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) := by
    letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
    haveI := isScalarTower_along (heckeAlphaBar (AlgebraicClosure ℚ) N q)
    haveI := isIntegral_along (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
    exact Place.ramificationIndex_pos (F := modularFunctionFieldBar N) V

  have hj : heckeAlphaBar (AlgebraicClosure ℚ) N q
      ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N))
        = PlaceSpecialization.ProlongationTuple.jFun N q :=
    Subtype.ext (coe_heckeAlphaBar N q _)
  have hpull : heckeAlphaBar (AlgebraicClosure ℚ) N q
      ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
      = PlaceSpecialization.ProlongationTuple.jFun N q
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
            (a : AlgebraicClosure ℚ) := by
    rw [map_sub, AlgHom.commutes, hj]
  have hup : 0 < V.ord (PlaceSpecialization.ProlongationTuple.jFun N q
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
          (a : AlgebraicClosure ℚ)) := by
    rw [← hpull, Place.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V]
    exact mul_pos (by exact_mod_cast he) ha

  have hne : PlaceSpecialization.ProlongationTuple.jFun N q
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
          (a : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hup
    exact lt_irrefl _ hup
  have hmem := add_mem (V.mem_of_ord_nonneg hne hup.le)
    (V.algebraMap_mem' (a : AlgebraicClosure ℚ))
  rwa [sub_add_cancel] at hmem

end NodeRing
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_fieldOver_nodeIntegersOver.NodeNormalization"

end NodeNormalization
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_fieldOver_nodeIntegersOver.NodeNormalization"

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (z : LaurentSeries (AlgebraicClosure ℚ)) (hz : z ∈ NodeLocalized.fieldOver (N * q) K) :
    ∃ x y : ↥(modularFunctionFieldBar (N * q)), x ∈ R.nodeIntegersOver K w ∧ y ∈ R.nodeIntegersOver K w ∧
      y ≠ 0 ∧ z * (y : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ)) := by

  have hzalg : IsAlgebraic ↥(NodeLocalized.jRing A K)
      (⟨z, hz⟩ : ↥(NodeLocalized.fieldOver (N * q) K)) :=
    (IsFractionRing.isAlgebraic_iff ↥(NodeLocalized.jRing A K) ↥(NodeNormalization.jField A K)
        ↥(NodeLocalized.fieldOver (N * q) K)).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨d, hd0, hint⟩ := hzalg.exists_integral_multiple
  have hc : IsIntegral ↥(NodeLocalized.jRing A K)
      ((d • (⟨z, hz⟩ : ↥(NodeLocalized.fieldOver (N * q) K)) :
          ↥(NodeLocalized.fieldOver (N * q) K)) : LaurentSeries (AlgebraicClosure ℚ)) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥(NodeLocalized.jRing A K)
        ↥(NodeLocalized.fieldOver (N * q) K) (LaurentSeries (AlgebraicClosure ℚ)))
      Subtype.coe_injective).2 hint
  have hcg : ((d • (⟨z, hz⟩ : ↥(NodeLocalized.fieldOver (N * q) K)) :
      ↥(NodeLocalized.fieldOver (N * q) K)) : LaurentSeries (AlgebraicClosure ℚ))
        = (d : LaurentSeries (AlgebraicClosure ℚ)) * z := by
    rw [Algebra.smul_def]
    rfl
  have hcC : (d : LaurentSeries (AlgebraicClosure ℚ)) * z
      ∈ NodeLocalized.jIntegralClosure (N * q) A K :=
    ⟨mul_mem (NodeNormalization.jRing_le_fieldOver (N * q) A K d.2) hz, by rw [← hcg]; exact hc⟩
  have hdC : (d : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.jIntegralClosure (N * q) A K :=
    NodeNormalization.jRing_le_jIntegralClosure A K (N * q) d.2

  have hss : IsSupersingularPlace q N k w := hw
  obtain ⟨-, ⟨hwj, -⟩, -⟩ := hss

  obtain ⟨S, h₁, -, h₂, -, -, ⟨hjS, -, -, -, -, -⟩, -⟩ :=
    ModularCurve.exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd N q hqN A
      (NodeNormalization.liesOverPrime_of_red red)
  obtain ⟨-, he₂⟩ := NodeNormalization.integers_eq_and_eq R (S 0) (S 1) h₁ h₂
  have hj₂ : jFun N q ∈ R.R₂.integers := by
    rw [he₂]
    exact hjS 1
  have hjq : ((jFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = jqModC (AlgebraicClosure ℚ) := by
    show coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ)
    rw [← jqModC_rat, coeffEmb, coeffMap_jqModC]

  have hC : ∀ (x : LaurentSeries (AlgebraicClosure ℚ))
      (hx : x ∈ NodeLocalized.jIntegralClosure (N * q) A K),
      (⟨x, NodeNormalization.fieldOver_le_modularFunctionFieldBar (N * q) K hx.1⟩ :
        ↥(modularFunctionFieldBar (N * q))) ∈ R.nodeIntegersOver K w := by
    intro x hx
    refine ⟨⟨?_, ?_, fun V hV => ?_⟩, hx.1⟩
    · exact NodeNormalization.mem_integersFst_of_mem_jIntegralClosure R K ⟨x, hx⟩
    · exact NodeNormalization.mem_valuationSubring_of_jRing_le (N * q) A K R.R₂.integers
        (NodeNormalization.mem_valuationSubring_of_mem_jRing (N * q) A K R.R₂.integers
          (fun a ha => (R.algebraMap_mem_nodeIntegers w ⟨a, ha⟩).2.1) hj₂ hjq) ⟨x, hx⟩
    · exact NodeNormalization.mem_valuationSubring_of_jRing_le (N * q) A K V.toValuationSubring
        (NodeNormalization.mem_valuationSubring_of_mem_jRing (N * q) A K V.toValuationSubring
          (fun a _ => V.algebraMap_mem' a)
          (NodeNormalization.jFun_mem_toValuationSubring (P := P) V (by rw [hV]; exact hwj)) hjq)
        ⟨x, hx⟩

  refine ⟨⟨(d : LaurentSeries (AlgebraicClosure ℚ)) * z,
      NodeNormalization.fieldOver_le_modularFunctionFieldBar (N * q) K hcC.1⟩,
    ⟨(d : LaurentSeries (AlgebraicClosure ℚ)),
      NodeNormalization.fieldOver_le_modularFunctionFieldBar (N * q) K hdC.1⟩,
    hC _ hcC, hC _ hdC, ?_, ?_⟩
  ·
    intro h0
    apply hd0
    apply Subtype.ext
    simpa using congrArg Subtype.val h0
  · exact mul_comm z (d : LaurentSeries (AlgebraicClosure ℚ))

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_fieldOver_nodeIntegersOver
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_fieldOver_nodeIntegersOver (solution)
