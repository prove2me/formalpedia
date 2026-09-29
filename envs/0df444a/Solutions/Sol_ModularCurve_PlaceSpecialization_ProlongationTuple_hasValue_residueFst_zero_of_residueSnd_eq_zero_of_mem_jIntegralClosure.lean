-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/5b5db274-a05d-5607-8b1a-fc7c94a8b414

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_IsIntegrallyClosed_exists_isPrime_height_eq_one_mem_ne_of_mul_eq_pow_mul
import Theorems.Thm_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure
import Theorems.Thm_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_nodeIntegersOver_of_mem_modularLocalizedAtPoint
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jFun_sub_jQFun_sub
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_NodeLocalized_exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_two
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_three
import Theorems.Thm_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_q_eq_two
import Theorems.Thm_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_q_eq_three
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁"
p2m_attr_erase "simp" "TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.ProjectiveLine.map_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply"
p2m_attr_erase "simp" "AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve ModularCurve
open ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace C3Aux

theorem fieldOver_le_bar (M : ℕ) [NeZero M] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : x ∈ fieldOver M K) :
    x ∈ modularFunctionFieldBar M := by
  have hle : fieldOver M K ≤ (modularFunctionFieldBar M).toSubfield := by
    unfold fieldOver
    rw [Subfield.closure_le]
    rintro y (⟨c, rfl⟩ | hy)
    · exact (modularFunctionFieldBar M).algebraMap_mem (c : AlgebraicClosure ℚ)
    · rcases hy with rfl | rfl
      · have h : jqModC (AlgebraicClosure ℚ) = coeffEmb (AlgebraicClosure ℚ) jq := by
          rw [← jqModC_rat, coeffEmb, coeffMap_jqModC]
        rw [h]
        exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M (jq_mem M))
      · have h : jqNModC (AlgebraicClosure ℚ) M = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M jq) := by
          rw [jqNModC, ← jqModC_rat, coeffEmb, coeffMap_qExpand, coeffMap_jqModC]
        rw [h]
        exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full M (dvd_refl M))
  exact hle hx

section Ideals

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

noncomputable def emb (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    ↥(jIntegralClosure (N * q) A K) →+* ↥(modularFunctionFieldBar (N * q)) where
  toFun c := ⟨(c : LaurentSeries (AlgebraicClosure ℚ)), fieldOver_le_bar (N * q) K c.2.1⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

@[scoped simp] theorem coe_emb (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (c : ↥(jIntegralClosure (N * q) A K)) :
    ((emb (N := N) (q := q) K c : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = c := rfl

theorem emb_injective (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    Function.Injective (emb (A := A) (N := N) (q := q) K) := by
  intro c d h
  exact Subtype.ext (congrArg (fun x : ↥(modularFunctionFieldBar (N * q)) => (x : LaurentSeries (AlgebraicClosure ℚ))) h)

variable (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
  (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
  (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)

include hqN hw

theorem emb_mem_nodeIntegers (c : ↥(jIntegralClosure (N * q) A K)) : emb K c ∈ R.nodeIntegers w :=
  (R.mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure hqN K w hw (emb K c) c.2).1

noncomputable def toFst : ↥(jIntegralClosure (N * q) A K) →+* ↥(R.R₁.integers) where
  toFun c := ⟨emb K c, (emb_mem_nodeIntegers R hqN K w hw c).1⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

noncomputable def toSnd : ↥(jIntegralClosure (N * q) A K) →+* ↥(R.R₂.integers) where
  toFun c := ⟨emb K c, (emb_mem_nodeIntegers R hqN K w hw c).2.1⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

@[scoped simp] theorem coe_toFst (c : ↥(jIntegralClosure (N * q) A K)) :
    ((toFst R hqN K w hw c : ↥(R.R₁.integers)) : ↥(modularFunctionFieldBar (N * q))) = emb K c := rfl
@[scoped simp] theorem coe_toSnd (c : ↥(jIntegralClosure (N * q) A K)) :
    ((toSnd R hqN K w hw c : ↥(R.R₂.integers)) : ↥(modularFunctionFieldBar (N * q))) = emb K c := rfl

noncomputable def P₁ : Ideal ↥(jIntegralClosure (N * q) A K) := RingHom.ker (R.residue₁.comp (toFst R hqN K w hw))

noncomputable def P₂ : Ideal ↥(jIntegralClosure (N * q) A K) := RingHom.ker (R.residue₂.comp (toSnd R hqN K w hw))

scoped instance isPrime_P₁ : (P₁ R hqN K w hw).IsPrime := RingHom.ker_isPrime _
scoped instance isPrime_P₂ : (P₂ R hqN K w hw).IsPrime := RingHom.ker_isPrime _

theorem mem_P₁_iff (c : ↥(jIntegralClosure (N * q) A K)) :
    c ∈ P₁ R hqN K w hw ↔ R.residue₁ (toFst R hqN K w hw c) = 0 := RingHom.mem_ker
theorem mem_P₂_iff (c : ↥(jIntegralClosure (N * q) A K)) :
    c ∈ P₂ R hqN K w hw ↔ R.residue₂ (toSnd R hqN K w hw c) = 0 := RingHom.mem_ker

noncomputable def resFstAt : ↥(jIntegralClosure (N * q) A K) →+* ↥(w.toValuationSubring) where
  toFun c := ⟨R.residue₁ (toFst R hqN K w hw c),
    (R.mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure hqN K w hw (emb K c) c.2).2.1 _⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

noncomputable def 𝔫₁ : Ideal ↥(jIntegralClosure (N * q) A K) :=
  RingHom.ker ((IsLocalRing.residue ↥(w.toValuationSubring)).comp (resFstAt R hqN K w hw))

scoped instance isPrime_𝔫₁ : (𝔫₁ R hqN K w hw).IsPrime := RingHom.ker_isPrime _

theorem mem_𝔫₁_iff (c : ↥(jIntegralClosure (N * q) A K)) :
    c ∈ 𝔫₁ R hqN K w hw ↔
      w.HasValue (R.residue₁ (toFst R hqN K w hw c) : ↥(modularFunctionFieldC k N)) (0 : k) := by
  rw [𝔫₁, RingHom.mem_ker, RingHom.comp_apply, Place.hasValue_iff]
  constructor
  · intro h
    exact ⟨(resFstAt R hqN K w hw c).2, by rw [map_zero]; exact h⟩
  · rintro ⟨hmem, hres⟩
    rw [map_zero] at hres
    exact hres

theorem P₁_le_𝔫₁ : P₁ R hqN K w hw ≤ 𝔫₁ R hqN K w hw := by
  intro c hc
  rw [mem_P₁_iff] at hc
  rw [𝔫₁, RingHom.mem_ker, RingHom.comp_apply]
  have : resFstAt R hqN K w hw c = 0 := Subtype.ext (by
    change R.residue₁ (toFst R hqN K w hw c) = ((0 : ↥(w.toValuationSubring)) : ↥(modularFunctionFieldC k N))
    rw [hc]; rfl)
  rw [this, map_zero]

end Ideals

section LocalRing

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

noncomputable scoped instance instIsNoetherianRing_jIntegralClosure (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    IsNoetherianRing ↥(jIntegralClosure (N * q) A K) :=
  (ModularCurve.jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level A N
    (Classical.choice (ModularCurve.nonempty_modularPolynomialData (N * q))) K).1

scoped instance instIsIntegrallyClosed_jIntegralClosure (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    IsIntegrallyClosed ↥(jIntegralClosure (N * q) A K) :=
  (ModularCurve.jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level A N
    (Classical.choice (ModularCurve.nonempty_modularPolynomialData (N * q))) K).2.1

variable (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
  (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
  (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)

abbrev D := Localization.AtPrime (𝔫₁ R hqN K w hw)

scoped instance instIsIntegrallyClosed_D : IsIntegrallyClosed (D R hqN K w hw) :=
  isIntegrallyClosed_of_isLocalization _ (𝔫₁ R hqN K w hw).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)

example : IsNoetherianRing (D R hqN K w hw) := inferInstance
example : IsDomain (D R hqN K w hw) := inferInstance

noncomputable def cst (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (c : ↥(coeffSubring A K)) :
    ↥(jIntegralClosure (N * q) A K) :=
  ⟨CharPReduction.constSeries (coeffSubring A K) c,
    Subfield.subset_closure (Or.inl ⟨⟨(c : AlgebraicClosure ℚ), c.2.2⟩, rfl⟩),
    isIntegral_algebraMap (R := ↥(jRing A K)) (A := LaurentSeries (AlgebraicClosure ℚ))
      (x := ⟨_, Subring.subset_closure (Or.inl ⟨c, rfl⟩)⟩)⟩

@[scoped simp] theorem coe_cst (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (c : ↥(coeffSubring A K)) :
    ((cst (N := N) (q := q) K c : ↥(jIntegralClosure (N * q) A K)) : LaurentSeries (AlgebraicClosure ℚ))
      = CharPReduction.constSeries (coeffSubring A K) c := rfl

end LocalRing

section S4Generic

private theorem _root_.AlgebraicCurve.Place.HasValue.add' {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}
    {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure.AlgebraicCurve.Place.HasValue.add'" "AlgebraicCurve.Place.HasValue.add'"
private theorem _root_.AlgebraicCurve.Place.HasValue.pow' {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}
    {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) : v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact v.hasValue_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure.AlgebraicCurve.Place.HasValue.pow'" "AlgebraicCurve.Place.HasValue.pow'"
private theorem _root_.AlgebraicCurve.Place.hasValue_evalAt_of_isRational {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.HasValue f (v.evalAt f) :=
  ⟨hf, (v.algebraMap_evalAt hv hf).symm⟩

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure.AlgebraicCurve.Place.hasValue_evalAt_of_isRational" "AlgebraicCurve.Place.hasValue_evalAt_of_isRational"

theorem qExpand_congr (L : Type*) [CommRing L] {M M' : ℕ} [NeZero M] [NeZero M'] (h : M = M') :
    qExpand L M = qExpand L M' := by
  subst h; rfl

theorem jqNModC_one_mul (L : Type*) [Field L] (M : ℕ) [NeZero M] :
    jqNModC L (1 * M) = jqNModC L M := by
  rw [jqNModC, jqNModC, qExpand_congr L (one_mul M)]

theorem jqModC_eq_coeffEmb : jqModC (AlgebraicClosure ℚ) = coeffEmb (AlgebraicClosure ℚ) jq := by
  rw [← jqModC_rat, coeffEmb, coeffMap_jqModC]

theorem jqNModC_eq_coeffEmb (M : ℕ) [NeZero M] :
    jqNModC (AlgebraicClosure ℚ) M = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M jq) := by
  rw [jqNModC, ← jqModC_rat, coeffEmb, coeffMap_qExpand, coeffMap_jqModC]

theorem coeffEmb_algebraMap_mem_fieldOver (M : ℕ) [NeZero M] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (r : ℚ) :
    coeffEmb (AlgebraicClosure ℚ) (algebraMap ℚ (LaurentSeries ℚ) r) ∈ fieldOver M K := by
  have h : coeffEmb (AlgebraicClosure ℚ) (algebraMap ℚ (LaurentSeries ℚ) r)
      = CharPReduction.constSeries K.toSubalgebra.toSubring ⟨algebraMap ℚ (AlgebraicClosure ℚ) r, K.algebraMap_mem r⟩ := by
    rw [coeffEmb, algebraMap_laurentSeries_eq_single, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
    rfl
  rw [h]
  exact Subfield.subset_closure (Or.inl ⟨_, rfl⟩)

theorem jqNModC_mem_fieldOver (N q : ℕ) [NeZero N] [NeZero q] [NeZero (N * q)] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    jqNModC (AlgebraicClosure ℚ) q ∈ fieldOver (N * q) K := by

  let E : IntermediateField ℚ (LaurentSeries ℚ) :=
    ((fieldOver (N * q) K).comap (coeffEmb (AlgebraicClosure ℚ))).toIntermediateField
      (fun r => coeffEmb_algebraMap_mem_fieldOver (N * q) K r)
  have hE : IntermediateField.adjoin ℚ {jq, qExpand ℚ (N * q) jq} ≤ E := by
    rw [IntermediateField.adjoin_le_iff]
    rintro y (rfl | rfl)
    · show coeffEmb (AlgebraicClosure ℚ) jq ∈ fieldOver (N * q) K
      rw [← jqModC_eq_coeffEmb]
      exact Subfield.subset_closure (Or.inr (Or.inl rfl))
    · show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * q) jq) ∈ fieldOver (N * q) K
      rw [← jqNModC_eq_coeffEmb]
      exact Subfield.subset_closure (Or.inr (Or.inr rfl))
  have hgen := ModularCurve.functionFieldGeneration (N * q) q (dvd_mul_left q N) inferInstance
  have := hE hgen
  rw [jqNModC_eq_coeffEmb]
  exact this

theorem jRing_le_fieldOver' (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (M : ℕ) [NeZero M] :
    jRing A K ≤ (fieldOver M K).toSubring := by
  rw [jRing, Subring.closure_le]
  rintro x (⟨c, rfl⟩ | hx)
  · exact Subfield.subset_closure (Or.inl ⟨⟨(c : AlgebraicClosure ℚ), (c.2).2⟩, rfl⟩)
  · rw [Set.mem_singleton_iff] at hx; subst hx
    exact Subfield.subset_closure (Or.inr (Or.inl rfl))

theorem isIntegral_jRing_jqNModC' (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    {q : ℕ} [NeZero q] (data : ModularPolynomialData q) :
    IsIntegral ↥(jRing A K) (jqNModC (AlgebraicClosure ℚ) (1 * q)) := by
  have hj : jqModC (AlgebraicClosure ℚ) ∈ jRing A K := Subring.subset_closure (Or.inr rfl)
  let φ : Polynomial ℤ →+* ↥(jRing A K) := Polynomial.eval₂RingHom (Int.castRingHom _) ⟨_, hj⟩
  refine ⟨data.Φ.map φ, data.monic.map φ, ?_⟩
  rw [Polynomial.eval₂_map]
  have h0 := ModularPolynomialData.eval_jqNModC_mul_eq_zero data (AlgebraicClosure ℚ) 1
  have hcomp : (algebraMap ↥(jRing A K) (LaurentSeries (AlgebraicClosure ℚ))).comp φ
      = (Polynomial.aeval (R := ℤ) (jqNModC (AlgebraicClosure ℚ) 1)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro n; simp [φ]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]
      show ((φ Polynomial.X : ↥(jRing A K)) : LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) 1
      rw [show φ Polynomial.X = ⟨_, hj⟩ from Polynomial.eval₂_X _ _]
      exact (qExpand_one_apply _).symm
  rw [hcomp]
  exact h0

theorem jqModC_mem_jIntegralClosure (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (M : ℕ) [NeZero M] : jqModC (AlgebraicClosure ℚ) ∈ jIntegralClosure M A K :=
  ⟨jRing_le_fieldOver' A K M (Subring.subset_closure (Or.inr rfl)),
    isIntegral_algebraMap (R := ↥(jRing A K)) (A := LaurentSeries (AlgebraicClosure ℚ))
      (x := ⟨_, Subring.subset_closure (Or.inr rfl)⟩)⟩

theorem jqNModC_mem_jIntegralClosure (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (N q : ℕ) [NeZero N] [NeZero q] [NeZero (N * q)] (data : ModularPolynomialData q) :
    jqNModC (AlgebraicClosure ℚ) (1 * q) ∈ jIntegralClosure (N * q) A K :=
  ⟨by rw [jqNModC_one_mul]; exact jqNModC_mem_fieldOver N q K, isIntegral_jRing_jqNModC' A K data⟩

end S4Generic

section S4Fibre

variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [DecidableEq k]

theorem hasValue_jGeomGen {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ ssPlaces q N k)
    {a : k} (ha : w.evalAt (jGeomGen k N) = a) : w.HasValue (jGeomGen k N) a := by
  rw [← ha]
  exact w.hasValue_evalAt_of_isRational hw.1 hw.2.1.1

variable (k N) in

theorem jGeomGen_sub_pow_ne_zero : jGeomGen k N - (jGeomGen k N ^ q) ^ q ≠ 0 := by
  intro h
  have hq : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (Fact.out : q.Prime).one_lt
  apply FiniteField.X_pow_card_sub_X_ne_zero k hq
  refine transcendental_iff.mp (transcendental_jqModC k) _ ?_
  have hc := congrArg (fun z : ↥(modularFunctionFieldC k N) => (z : LaurentSeries k)) h
  simp only [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, coe_jGeomGen, ZeroMemClass.coe_zero] at hc
  have hc' : (jqModC k ^ q) ^ q = jqModC k := (sub_eq_zero.mp hc).symm
  rw [map_sub, map_pow, Polynomial.aeval_X, pow_two, pow_mul, hc', sub_self]

end S4Fibre

section S4Tuple

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

noncomputable def cstHom (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    ↥(coeffSubring A K) →+* ↥(jIntegralClosure (N * q) A K) where
  toFun := cst (N := N) (q := q) K
  map_one' := Subtype.ext (by rw [coe_cst, map_one]; rfl)
  map_mul' _ _ := Subtype.ext (by rw [coe_cst, map_mul]; rfl)
  map_zero' := Subtype.ext (by rw [coe_cst, map_zero]; rfl)
  map_add' _ _ := Subtype.ext (by rw [coe_cst, map_add]; rfl)

@[scoped simp] theorem cstHom_apply (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (c : ↥(coeffSubring A K)) :
    cstHom (N := N) (q := q) K c = cst K c := rfl

variable (data) in

noncomputable def mEC (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥(jIntegralClosure (N * q) A K) :=
  MvPolynomial.eval₂Hom (cstHom K)
    ![⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_jIntegralClosure A K (N * q)⟩,
      ⟨jqNModC (AlgebraicClosure ℚ) (1 * q), jqNModC_mem_jIntegralClosure A K N q data⟩]

theorem coe_mEC (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    ((mEC (N := N) data K p : ↥(jIntegralClosure (N * q) A K)) : LaurentSeries (AlgebraicClosure ℚ))
      = modularEval (1 * q) (coeffSubring A K) p := by
  have h : ((jIntegralClosure (N * q) A K).subtype).comp (mEC (N := N) data K) = modularEval (1 * q) (coeffSubring A K) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [RingHom.comp_apply, mEC, MvPolynomial.eval₂Hom_C, modularEval, MvPolynomial.eval₂Hom_C]
      rfl
    · intro i
      rw [RingHom.comp_apply, mEC, MvPolynomial.eval₂Hom_X', modularEval, MvPolynomial.eval₂Hom_X']
      fin_cases i <;> rfl
  exact RingHom.congr_fun h p

variable (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
  (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
  (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)

noncomputable abbrev ψ : ↥(jIntegralClosure (N * q) A K) →+* ↥(modularFunctionFieldC k N) :=
  R.residue₁.comp (toFst R hqN K w hw)

include hqN hw

theorem ψ_jq :
    ψ R hqN K w hw ⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_jIntegralClosure A K (N * q)⟩ = jGeomGen k N := by
  obtain ⟨h₁, -, -, -, e1, -, -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN (0 : A)
  have hx : toFst R hqN K w hw ⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_jIntegralClosure A K (N * q)⟩
      = ⟨ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((0 : A) : AlgebraicClosure ℚ), h₁⟩ := by
    apply Subtype.ext; apply Subtype.ext
    show jqModC (AlgebraicClosure ℚ) = ((ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((0 : A) : AlgebraicClosure ℚ) : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
    rw [ZeroMemClass.coe_zero, map_zero, sub_zero]
    exact jqModC_eq_coeffEmb
  rw [RingHom.comp_apply, hx, e1, map_zero, map_zero, sub_zero]

theorem ψ_jqq :
    ψ R hqN K w hw ⟨jqNModC (AlgebraicClosure ℚ) (1 * q), jqNModC_mem_jIntegralClosure A K N q data⟩ = jGeomGen k N ^ q := by
  obtain ⟨-, -, h₃, -, -, -, e3, -⟩ := R.residue_jFun_sub_jQFun_sub hqN (0 : A)
  have hx : toFst R hqN K w hw ⟨jqNModC (AlgebraicClosure ℚ) (1 * q), jqNModC_mem_jIntegralClosure A K N q data⟩
      = ⟨ProlongationTuple.jQFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((0 : A) : AlgebraicClosure ℚ), h₃⟩ := by
    apply Subtype.ext; apply Subtype.ext
    show jqNModC (AlgebraicClosure ℚ) (1 * q) = ((ProlongationTuple.jQFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((0 : A) : AlgebraicClosure ℚ) : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
    rw [ZeroMemClass.coe_zero, map_zero, sub_zero, jqNModC_one_mul, jqNModC_eq_coeffEmb]
    rfl
  rw [RingHom.comp_apply, hx, e3, map_zero, map_zero, sub_zero]

theorem ψ_cst (c : ↥(coeffSubring A K)) :
    ψ R hqN K w hw (cst K c) = algebraMap k ↥(modularFunctionFieldC k N) (redRestrict red K c) := by
  let cA : A := ⟨(c : AlgebraicClosure ℚ), c.2.1⟩
  obtain ⟨h₁, -, -, -, e1, -, -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN (0 : A)
  obtain ⟨h₁', -, -, -, e1', -, -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN cA
  have hx : toFst R hqN K w hw (cst K c)
      = ⟨ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((0 : A) : AlgebraicClosure ℚ), h₁⟩
        - ⟨ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((cA : A) : AlgebraicClosure ℚ), h₁'⟩ := by
    apply Subtype.ext; apply Subtype.ext
    show CharPReduction.constSeries (coeffSubring A K) c
      = (((ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((0 : A) : AlgebraicClosure ℚ))
          - (ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((cA : A) : AlgebraicClosure ℚ))
          : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
    rw [ZeroMemClass.coe_zero, map_zero, sub_zero, sub_sub_cancel]
    rfl
  rw [RingHom.comp_apply, hx, map_sub, e1, e1', map_zero, map_zero, sub_zero, sub_sub_cancel]
  rfl

theorem ψ_mEC (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    ψ R hqN K w hw (mEC (N := N) data K p)
      = MvPolynomial.eval₂Hom ((algebraMap k ↥(modularFunctionFieldC k N)).comp (redRestrict red K))
          ![jGeomGen k N, jGeomGen k N ^ q] p := by
  have h : (ψ R hqN K w hw).comp (mEC (N := N) data K)
      = MvPolynomial.eval₂Hom ((algebraMap k ↥(modularFunctionFieldC k N)).comp (redRestrict red K))
          ![jGeomGen k N, jGeomGen k N ^ q] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, mEC, MvPolynomial.eval₂Hom_C, cstHom_apply, ψ_cst]
      rfl
    · intro i
      rw [RingHom.comp_apply, mEC, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
      fin_cases i
      · exact ψ_jq R hqN K w hw
      · exact ψ_jqq R hqN K w hw
  exact RingHom.congr_fun h p

theorem hasValue_ψ_mEC {a : k} (ha : w.evalAt (jGeomGen k N) = a) (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    w.HasValue (ψ R hqN K w hw (mEC (N := N) data K p)) (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) p) := by
  rw [ψ_mEC R hqN K w hw]
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.eval₂Hom_C, pointEval, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    exact w.hasValue_algebraMap _
  | add p r hp hr => rw [map_add, map_add]; exact hp.add' hr
  | mul_X p i hp =>
    rw [map_mul, map_mul, MvPolynomial.eval₂Hom_X', pointEval, MvPolynomial.eval₂Hom_X']
    refine hp.mul ?_
    fin_cases i
    · exact hasValue_jGeomGen hw ha
    · exact (hasValue_jGeomGen hw ha).pow' q

theorem mEC_mem_𝔫₁_iff {a : k} (ha : w.evalAt (jGeomGen k N) = a) (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    mEC (N := N) data K p ∈ 𝔫₁ R hqN K w hw ↔ pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) p = 0 := by
  rw [mem_𝔫₁_iff]
  constructor
  · intro h; exact (hasValue_ψ_mEC R hqN K w hw ha p).unique h
  · intro h; rw [← h]; exact hasValue_ψ_mEC R hqN K w hw ha p

include R in

theorem pointEval_eq_of_modularEval_eq {a : k} (ha : w.evalAt (jGeomGen k N) = a) {p r : MvPolynomial (Fin 2) ↥(coeffSubring A K)}
    (h : modularEval (1 * q) (coeffSubring A K) p = modularEval (1 * q) (coeffSubring A K) r) :
    pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) p = pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) r := by
  have hC : mEC (N := N) data K p = mEC (N := N) data K r := Subtype.ext (by rw [coe_mEC, coe_mEC, h])
  have h1 := hasValue_ψ_mEC R hqN K w hw ha p
  rw [hC] at h1
  exact h1.unique (hasValue_ψ_mEC R hqN K w hw ha r)

theorem mEC_notMem_P₁ {a : k} (ha : w.evalAt (jGeomGen k N) = a) {p : MvPolynomial (Fin 2) ↥(coeffSubring A K)}
    (hp : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) p ≠ 0) :
    mEC (N := N) data K p ∉ P₁ R hqN K w hw := by
  rw [mem_P₁_iff]
  exact (hasValue_ψ_mEC R hqN K w hw ha p).ne_zero hp

end S4Tuple

section LocalRing

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

variable (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
  (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
  (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)

include hqN hw in

theorem datum_of_crossing (a : k) (ha : w.evalAt (jGeomGen k N) = a) (ha2 : a ^ (q ^ 2) = a)
    (ϖ : ↥(coeffSubring A K)) (hϖ0 : redRestrict red K ϖ = 0) (E : ℕ)
    (G' H' w₀ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (hunit : IsUnit w₀)
    (hGH : G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ^ E * w₀)
    (hH : H' ∈ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
        (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))})
    (hy : (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
        ∈ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'}) :
    ∃ (r₁ r₂ num : ↥(jIntegralClosure (N * q) A K)),
      r₂ ∉ P₁ R hqN K w hw ∧ r₂ ∈ 𝔫₁ R hqN K w hw ∧ num ∉ 𝔫₁ R hqN K w hw ∧
      r₁ * r₂ = cst K ϖ ^ E * num := by
  classical
  have hwd : ∀ {p r : MvPolynomial (Fin 2) ↥(coeffSubring A K)}, (modularEval (1 * q) (coeffSubring A K)) p = (modularEval (1 * q) (coeffSubring A K)) r → (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q)) p = (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q)) r :=
    fun h => pointEval_eq_of_modularEval_eq R hqN K w hw ha h

  obtain ⟨rG, sG, hsG, hG⟩ := (mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).mp G'.2
  obtain ⟨rH, sH, hsH, hHp⟩ := (mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).mp H'.2
  obtain ⟨rw, sw, hsw, hwp⟩ := (mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).mp w₀.2

  obtain ⟨v, hv⟩ := hunit.exists_right_inv
  obtain ⟨rv, sv, hsv, hvp⟩ := (mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).mp v.2
  have hv' : (w₀ : LaurentSeries (AlgebraicClosure ℚ)) * (v : LaurentSeries (AlgebraicClosure ℚ)) = 1 := by
    have := congrArg Subtype.val hv
    simp only [Subring.coe_mul, Subring.coe_one] at this
    exact this
  have hrw : (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q)) rw ≠ 0 := by
    have h1 : (modularEval (1 * q) (coeffSubring A K)) (rw * rv) = (modularEval (1 * q) (coeffSubring A K)) (sw * sv) := by
      rw [map_mul, map_mul, ← hwp, ← hvp]
      linear_combination ((modularEval (1 * q) (coeffSubring A K)) sw * (modularEval (1 * q) (coeffSubring A K)) sv) * hv'
    have h2 := hwd h1
    rw [map_mul, map_mul] at h2
    intro h0
    rw [h0, zero_mul] at h2
    exact mul_ne_zero hsw hsv h2.symm

  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp hH
  obtain ⟨rα, sα, hsα, hα⟩ := (mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).mp α.2
  obtain ⟨rβ, sβ, hsβ, hβ⟩ := (mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).mp β.2
  have eq0 : (α : LaurentSeries (AlgebraicClosure ℚ)) * (modularEval (1 * q) (coeffSubring A K)) (MvPolynomial.C ϖ)
      + (β : LaurentSeries (AlgebraicClosure ℚ)) * (modularEval (1 * q) (coeffSubring A K)) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)
      = (H' : LaurentSeries (AlgebraicClosure ℚ)) := by
    have := congrArg Subtype.val hαβ
    simp only [Subring.coe_add, Subring.coe_mul] at this
    exact this
  have key1 : (modularEval (1 * q) (coeffSubring A K)) (rH * sα * sβ)
      = (modularEval (1 * q) (coeffSubring A K)) (rα * sβ * sH * MvPolynomial.C ϖ + rβ * sα * sH * (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) := by
    simp only [map_mul, map_add]
    rw [← hHp, ← hα, ← hβ]
    linear_combination (-((modularEval (1 * q) (coeffSubring A K)) sα * (modularEval (1 * q) (coeffSubring A K)) sβ * (modularEval (1 * q) (coeffSubring A K)) sH)) * eq0
  have hrH0 : (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q)) rH = 0 := by
    have h2 := hwd key1
    simp only [map_mul, map_add, map_sub, map_pow, pointEval, MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h2
    rw [← pow_mul, ← sq, ha2, sub_self, mul_zero, add_zero, hϖ0, mul_zero] at h2
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · exact h4
      · exact absurd h4 hsα
    · exact absurd h3 hsβ

  obtain ⟨γ, δ, hγδ⟩ := Ideal.mem_span_pair.mp hy
  obtain ⟨rγ, sγ, hsγ, hγ⟩ := (mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).mp γ.2
  obtain ⟨rδ, sδ, hsδ, hδ⟩ := (mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).mp δ.2
  have eq1 : (γ : LaurentSeries (AlgebraicClosure ℚ)) * (modularEval (1 * q) (coeffSubring A K)) (MvPolynomial.C ϖ)
      + (δ : LaurentSeries (AlgebraicClosure ℚ)) * (H' : LaurentSeries (AlgebraicClosure ℚ))
      = (modularEval (1 * q) (coeffSubring A K)) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q) := by
    have := congrArg Subtype.val hγδ
    simp only [Subring.coe_add, Subring.coe_mul] at this
    exact this
  have key2 : (modularEval (1 * q) (coeffSubring A K)) ((MvPolynomial.X 0 - MvPolynomial.X 1 ^ q) * sγ * sδ * sH)
      = (modularEval (1 * q) (coeffSubring A K)) (rγ * sδ * sH * MvPolynomial.C ϖ + rδ * sγ * rH) := by
    simp only [map_mul, map_add]
    rw [← hHp, ← hγ, ← hδ]
    linear_combination (-((modularEval (1 * q) (coeffSubring A K)) sγ * (modularEval (1 * q) (coeffSubring A K)) sδ * (modularEval (1 * q) (coeffSubring A K)) sH)) * eq1
  have key2C : mEC (N := N) data K (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q) * mEC data K sγ * mEC data K sδ * mEC data K sH
      = mEC data K rγ * mEC data K sδ * mEC data K sH * mEC data K (MvPolynomial.C ϖ)
        + mEC data K rδ * mEC data K sγ * mEC data K rH := by
    apply Subtype.ext
    simp only [Subring.coe_mul, Subring.coe_add, coe_mEC, ← map_mul, ← map_add]
    exact key2
  have hψs : ∀ {s : MvPolynomial (Fin 2) ↥(coeffSubring A K)}, (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q)) s ≠ 0 → ψ R hqN K w hw (mEC (N := N) data K s) ≠ 0 :=
    fun hs => (hasValue_ψ_mEC R hqN K w hw ha _).ne_zero hs
  have hrH1 : ψ R hqN K w hw (mEC (N := N) data K rH) ≠ 0 := by
    intro h0
    have h2 := congrArg (ψ R hqN K w hw) key2C
    simp only [map_mul, map_add] at h2
    have hC : ψ R hqN K w hw (mEC (N := N) data K (MvPolynomial.C ϖ)) = 0 := by
      rw [ψ_mEC R hqN K w hw, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, hϖ0, map_zero]
    have hY : ψ R hqN K w hw (mEC (N := N) data K (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q))
        = jGeomGen k N - (jGeomGen k N ^ q) ^ q := by
      rw [ψ_mEC R hqN K w hw, map_sub, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
      rfl
    rw [h0, mul_zero, add_zero, hC, mul_zero, hY] at h2
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (jGeomGen_sub_pow_ne_zero N k) (hψs hsγ)) (hψs hsδ)) (hψs hsH) h2

  have hGH' : (G' : LaurentSeries (AlgebraicClosure ℚ)) * (H' : LaurentSeries (AlgebraicClosure ℚ))
      = (modularEval (1 * q) (coeffSubring A K)) (MvPolynomial.C ϖ) ^ E * (w₀ : LaurentSeries (AlgebraicClosure ℚ)) := by
    have := congrArg Subtype.val hGH
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow] at this
    exact this
  have key3 : (modularEval (1 * q) (coeffSubring A K)) (rG * sw) * (modularEval (1 * q) (coeffSubring A K)) rH = (modularEval (1 * q) (coeffSubring A K)) (MvPolynomial.C ϖ) ^ E * (modularEval (1 * q) (coeffSubring A K)) (rw * sG * sH) := by
    simp only [map_mul]
    rw [← hG, ← hHp, ← hwp]
    linear_combination ((modularEval (1 * q) (coeffSubring A K)) sG * (modularEval (1 * q) (coeffSubring A K)) sw * (modularEval (1 * q) (coeffSubring A K)) sH) * hGH'
  refine ⟨mEC data K (rG * sw), mEC data K rH, mEC data K (rw * sG * sH), ?_, ?_, ?_, ?_⟩
  · rw [mem_P₁_iff]; exact hrH1
  · exact (mEC_mem_𝔫₁_iff R hqN K w hw ha rH).mpr hrH0
  · rw [mEC_mem_𝔫₁_iff R hqN K w hw ha, map_mul, map_mul]
    exact mul_ne_zero (mul_ne_zero hrw hsG) hsH
  · apply Subtype.ext
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, coe_mEC, coe_cst]
    rw [show CharPReduction.constSeries (coeffSubring A K) ϖ = (modularEval (1 * q) (coeffSubring A K)) (MvPolynomial.C ϖ) from
      (MvPolynomial.eval₂Hom_C _ _ _).symm]
    exact key3

include hqN hw in

theorem levelOne_datum (a : k) (ha : w.evalAt (jGeomGen k N) = a)
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a) :
    ∃ (e : ℕ) (ϖ : ↥(coeffSubring A K)) (r₁ r₂ num : ↥(jIntegralClosure (N * q) A K)),
      ϖ ≠ 0 ∧
      r₂ ∉ P₁ R hqN K w hw ∧ r₂ ∈ 𝔫₁ R hqN K w hw ∧ num ∉ 𝔫₁ R hqN K w hw ∧
      r₁ * r₂ = cst K ϖ ^ e * num ∧
      (∃ d : ↥(jIntegralClosure (N * q) A K), ((q : ℕ) : ↥(jIntegralClosure (N * q) A K)) = cst K ϖ * d) := by
  classical

  have hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A := by
    intro c
    rw [← R.redBar_residue, map_eq_zero_iff _ R.redBar.injective, IsLocalRing.residue_eq_zero_iff]
  obtain ⟨ϖ, hϖ, eK, ε, heK, hε, hqϖ⟩ :=
    ModularCurve.NodeLocalized.exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul red hker K
  have hϖ0 : redRestrict red K ϖ = 0 := (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩
  have hϖne : ϖ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.one_le_iff_ne_zero.mp heK), zero_mul] at hqϖ
    have : ((q : ℕ) : AlgebraicClosure ℚ) = 0 := by
      have := congrArg (fun z : ↥(coeffSubring A K) => (z : AlgebraicClosure ℚ)) hqϖ
      simpa using this
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) this
  have hqd : ∃ d : ↥(jIntegralClosure (N * q) A K), ((q : ℕ) : ↥(jIntegralClosure (N * q) A K)) = cst K ϖ * d := by
    refine ⟨cstHom (N := N) (q := q) K (ϖ ^ (eK - 1) * ε), ?_⟩
    rw [← cstHom_apply (N := N) (q := q), ← map_mul, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel heK, ← hqϖ, map_natCast]
  have hss : a ∈ ssJSet q k := ha ▸ hw.2.2
  have ha2 : a ^ (q ^ 2) = a := ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet q hss

  have main : ∃ (E : ℕ) (r₁ r₂ num : ↥(jIntegralClosure (N * q) A K)),
      r₂ ∉ P₁ R hqN K w hw ∧ r₂ ∈ 𝔫₁ R hqN K w hw ∧ num ∉ 𝔫₁ R hqN K w hw ∧
      r₁ * r₂ = cst K ϖ ^ E * num := by
    by_cases hq5 : 5 ≤ q
    · obtain ⟨eK', ε', -, -, -, G', H', w₀, hunit, hGH, -, -, -, -, -, -, hHspan⟩ :=
        ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring red a hss ha2 hq5 K x hx ϖ hϖ
      have hH := (hHspan ▸ Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)) :
        H' ∈ Ideal.span {_, _})
      have hy := (hHspan.symm ▸ Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)) :
        (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ∈ Ideal.span {_, _})
      obtain ⟨r₁, r₂, num, h1, h2, h3, h4⟩ :=
        datum_of_crossing R hqN K w hw a ha ha2 ϖ hϖ0 _ G' H' w₀ hunit hGH hH hy
      exact ⟨_, r₁, r₂, num, h1, h2, h3, h4⟩
    · have hq23 : q = 2 ∨ q = 3 := by
        have hp : q.Prime := Fact.out
        have h2 := hp.two_le
        interval_cases q
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd hp (by decide)
      rcases hq23 with rfl | rfl
      ·
        have ha0 : a = 0 := ModularCurve.eq_zero_of_mem_ssJSet_two a hss ha2
        subst ha0
        obtain ⟨eK', ε', -, -, -, G', H', w₀, hunit, hGH, -, -, -, -, -, -, hHspan⟩ :=
          ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_q_eq_two red rfl K ϖ hϖ
        have hH := (hHspan ▸ Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)) :
          H' ∈ Ideal.span {_, _})
        have hy := (hHspan.symm ▸ Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)) :
          (⟨modularEval (1 * 2) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ 2),
            modularEval_mem_modularLocalizedAtPoint (1 * 2) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ 2) _⟩ :
            ↥(modularLocalizedAtPoint (1 * 2) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ 2))) ∈ Ideal.span {_, _})
        obtain ⟨r₁, r₂, num, h1, h2, h3, h4⟩ :=
          datum_of_crossing R hqN K w hw 0 ha ha2 ϖ hϖ0 _ G' H' w₀ hunit hGH hH hy
        exact ⟨_, r₁, r₂, num, h1, h2, h3, h4⟩
      ·
        have ha0 : a = 0 := ModularCurve.eq_zero_of_mem_ssJSet_three a hss ha2
        subst ha0
        obtain ⟨eK', ε', -, -, -, G', H', w₀, hunit, hGH, -, -, -, -, -, -, hHspan⟩ :=
          ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_q_eq_three red rfl K ϖ hϖ
        have hH := (hHspan ▸ Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)) :
          H' ∈ Ideal.span {_, _})
        have hy := (hHspan.symm ▸ Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)) :
          (⟨modularEval (1 * 3) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ 3),
            modularEval_mem_modularLocalizedAtPoint (1 * 3) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ 3) _⟩ :
            ↥(modularLocalizedAtPoint (1 * 3) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ 3))) ∈ Ideal.span {_, _})
        obtain ⟨r₁, r₂, num, h1, h2, h3, h4⟩ :=
          datum_of_crossing R hqN K w hw 0 ha ha2 ϖ hϖ0 _ G' H' w₀ hunit hGH hH hy
        exact ⟨_, r₁, r₂, num, h1, h2, h3, h4⟩
  obtain ⟨E, r₁, r₂, num, h1, h2, h3, h4⟩ := main
  exact ⟨E, ϖ, r₁, r₂, num, hϖne, h1, h2, h3, h4, hqd⟩

include hqN hw in

theorem P₂_le_𝔫₁ (a : k) (ha : w.evalAt (jGeomGen k N) = a)
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a) :
    P₂ R hqN K w hw ≤ 𝔫₁ R hqN K w hw := by
  classical
  obtain ⟨e, ϖ, r₁, r₂, num, hϖ0, hr₂P, hr₂n, hnum, heq, ⟨dq, hdq⟩⟩ :=
    levelOne_datum R hqN K w hw a ha x hx

  let Dl := D R hqN K w hw
  let f := algebraMap (↥(jIntegralClosure (N * q) A K)) Dl
  have hdisj₁ : Disjoint (↑(𝔫₁ R hqN K w hw).primeCompl : Set ↥(jIntegralClosure (N * q) A K)) ↑(P₁ R hqN K w hw) :=
    Set.disjoint_left.mpr fun y hy hyP => hy (P₁_le_𝔫₁ R hqN K w hw hyP)
  haveI hQ₁ : (Ideal.map f (P₁ R hqN K w hw)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (𝔫₁ R hqN K w hw).primeCompl Dl _ inferInstance hdisj₁
  have hfinj : Function.Injective f :=
    IsLocalization.injective Dl (Ideal.primeCompl_le_nonZeroDivisors (𝔫₁ R hqN K w hw))
  have hϖD : f (cst K ϖ) ≠ 0 := by
    intro h0
    apply hϖ0
    have h1 : cst K ϖ = 0 := hfinj (by rw [h0, map_zero])
    have h2 : ((ϖ : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) = 0 := by
      have h3 := congrArg (fun y : ↥(jIntegralClosure (N * q) A K) => (y : LaurentSeries (AlgebraicClosure ℚ))) h1
      simp only [coe_cst, ZeroMemClass.coe_zero] at h3
      have h4 : (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) (ϖ : AlgebraicClosure ℚ) = 0 := h3
      exact (map_eq_zero_iff _ (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).injective).mp h4
    exact Subtype.ext h2
  have hmax : ∀ y : ↥(jIntegralClosure (N * q) A K), f y ∈ IsLocalRing.maximalIdeal Dl ↔ y ∈ 𝔫₁ R hqN K w hw :=
    fun y => IsLocalization.AtPrime.to_map_mem_maximal_iff Dl (𝔫₁ R hqN K w hw) y
  have hH : ¬ IsUnit (f r₂) := by
    intro hunit
    exact (IsLocalRing.mem_maximalIdeal _).mp ((hmax r₂).mpr hr₂n) hunit
  have hcomap₁ : Ideal.comap f (Ideal.map f (P₁ R hqN K w hw)) = P₁ R hqN K w hw :=
    IsLocalization.comap_map_of_isPrime_disjoint (𝔫₁ R hqN K w hw).primeCompl Dl inferInstance hdisj₁
  have hHQ₁ : f r₂ ∉ Ideal.map f (P₁ R hqN K w hw) := by
    intro hmem
    apply hr₂P
    rw [← hcomap₁]
    exact Ideal.mem_comap.mpr hmem
  have hu : IsUnit (f num) := IsLocalization.map_units Dl (⟨num, hnum⟩ : (𝔫₁ R hqN K w hw).primeCompl)
  have hGH : f r₁ * f r₂ = f (cst K ϖ) ^ e * f num := by
    rw [← map_mul, heq, map_mul, map_pow]
  obtain ⟨Q, hQ, hQht, hϖQ, hQne⟩ :=
    IsIntegrallyClosed.exists_isPrime_height_eq_one_mem_ne_of_mul_eq_pow_mul (D := Dl)
      (f (cst K ϖ)) hϖD (Ideal.map f (P₁ R hqN K w hw)) (f r₁) (f r₂) (f num) e hH hHQ₁ hu hGH

  haveI := hQ
  let Pc : Ideal ↥(jIntegralClosure (N * q) A K) := Ideal.comap f Q
  have hPc_le : Pc ≤ 𝔫₁ R hqN K w hw := by
    intro y hy
    have hQle : Q ≤ IsLocalRing.maximalIdeal Dl := IsLocalRing.le_maximalIdeal hQ.ne_top
    exact (hmax y).mp (hQle (Ideal.mem_comap.mp hy))
  have hPc_ht : Pc.height = 1 := by
    have h := IsLocalization.height_under (𝔫₁ R hqN K w hw).primeCompl (A := Dl) Q
    rw [hQht] at h
    exact h
  have hqPc : ((q : ℕ) : ↥(jIntegralClosure (N * q) A K)) ∈ Pc := by
    rw [hdq]
    exact Pc.mul_mem_right _ (Ideal.mem_comap.mpr hϖQ)
  rcases R.forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one hqN K Pc hPc_ht hqPc
    with hfst | hsnd
  ·
    exfalso
    apply hQne
    have hPc : Pc = P₁ R hqN K w hw := by
      ext y
      have hy := hfst (emb K y) y.2
      have hyy : (⟨((emb K y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)), y.2⟩ :
          ↥(jIntegralClosure (N * q) A K)) = y := Subtype.ext rfl
      rw [hyy] at hy
      rw [hy, mem_P₁_iff]
      constructor
      · rintro ⟨h₁, h0⟩
        have : (toFst R hqN K w hw y : ↥(R.R₁.integers)) = ⟨emb K y, h₁⟩ := Subtype.ext rfl
        rw [this]; exact h0
      · intro h0
        exact ⟨(toFst R hqN K w hw y).2, h0⟩
    calc Q = Ideal.map f (Ideal.comap f Q) :=
          (IsLocalization.map_comap (𝔫₁ R hqN K w hw).primeCompl Dl Q).symm
      _ = Ideal.map f (P₁ R hqN K w hw) := by rw [show Ideal.comap f Q = Pc from rfl, hPc]
  ·
    intro c hc
    apply hPc_le
    have hy := hsnd (emb K c) c.2
    have hcc : (⟨((emb K c : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)), c.2⟩ :
        ↥(jIntegralClosure (N * q) A K)) = c := Subtype.ext rfl
    rw [hcc] at hy
    rw [hy]
    rw [mem_P₂_iff] at hc
    exact ⟨(toSnd R hqN K w hw c).2, hc⟩

end LocalRing

end C3Aux
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure.C3Aux"

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k]
    (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (a : k) (ha : w.evalAt (jGeomGen k N) = a)
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (t : ↥(modularFunctionFieldBar (N * q)))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K)
    (h₂ : t ∈ R.R₂.integers) (ht₂ : R.residue₂ ⟨t, h₂⟩ = 0) :
    ∃ h₁ : t ∈ R.R₁.integers, w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k) := by
  set c : ↥(jIntegralClosure (N * q) A K) := ⟨(t : LaurentSeries (AlgebraicClosure ℚ)), ht⟩ with hc
  have hemb : C3Aux.emb K c = t := Subtype.ext rfl
  have hP₂ : c ∈ C3Aux.P₂ R hqN K w hw := by
    rw [C3Aux.mem_P₂_iff]
    have h : (C3Aux.toSnd R hqN K w hw c : ↥(R.R₂.integers)) = ⟨t, h₂⟩ := Subtype.ext hemb
    rw [h]
    exact ht₂
  have h𝔫 : c ∈ C3Aux.𝔫₁ R hqN K w hw := C3Aux.P₂_le_𝔫₁ R hqN K w hw a ha x hx hP₂
  rw [C3Aux.mem_𝔫₁_iff] at h𝔫
  refine ⟨hemb ▸ (C3Aux.emb_mem_nodeIntegers R hqN K w hw c).1, ?_⟩
  convert h𝔫 using 2
  first
    | rfl
    | exact Subtype.ext hemb.symm
    | (apply Subtype.ext; simp [hemb, hc])

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure (solution)
