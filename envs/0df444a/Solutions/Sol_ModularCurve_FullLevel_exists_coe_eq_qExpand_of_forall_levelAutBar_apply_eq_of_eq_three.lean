-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/7fc239a5-75f6-5353-b527-509e2a79d97b

import Definitions.Def_ModularCurve_FullLevelJacobian
import Theorems.Thm_ModularCurve_FullLevel_exists_finite_subgroup_forall_levelAutBar_mem
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_apply_eq_self_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0
import Theorems.Thm_ModularCurve_FullLevel_mul_card_ge_of_forall_levelAutBar_mem_of_eq_three
import Theorems.Thm_ModularCurve_FullLevel_adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq_of_eq_three
p2m_attr_erase "instance" "ModularCurve.FullLevel.SemistableCovering.instAlgebraSS ModularCurve.FullLevel.SemistableCovering.instFieldIg ModularCurve.FullLevel.SemistableCovering.instFieldSS ModularCurve.FullLevel.SemistableCovering.instAlgebraIg ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.FullLevel.SemistableCovering.mk.sizeOf_spec ModularCurve.FullLevel.SemistableCovering.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.JZeroSemistableSpecialization.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.injEq AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicCurve.SemilinearAut.coe_admissibleMap AlgebraicCurve.SemilinearAut.gluingMap_apply AlgebraicCurve.GluedPic0.glueMap_mk AlgebraicCurve.SemilinearAut.nodePerm_apply AlgebraicCurve.SemilinearAut.baseAutUnitsHom_apply ModularCurve.jqNModC_one ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply AlgebraicCurve.ComponentChart.comap_placeMap AlgebraicCurve.ComponentChart.comap_residue_apply AlgebraicCurve.ComponentChart.coe_comapIntegersEquiv AlgebraicCurve.ComponentChart.comapResidue_apply AlgebraicCurve.ComponentChart.comap_integers AlgebraicCurve.ComponentChart.comap_dom AlgebraicCurve.ComponentChart.mem_comapIntegers AlgebraicCurve.Annulus.comap_param AlgebraicCurve.Annulus.comap_dom AlgebraicCurve.Annulus.comap_modulus AlgebraicCurve.ComponentChart.mem_comap_integers AlgebraicCurve.ComponentChart.comap_nodes AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_FullLevel_exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq_of_eq_three.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq_of_eq_three.ModularCurve.FullLevel CongruenceSubgroup"
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC qExpand qExpand_single algebraMap_laurentSeries_eq_single laurentBaseChange"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "fieldBar Idx levelAutBar exists_finite_subgroup_forall_levelAutBar_mem levelAutBar_apply_eq_self_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0 mul_card_ge_of_forall_levelAutBar_mem_of_eq_three adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three"
namespace FixedFieldProof
p2m_open "ModularCurve.FullLevel ModularCurve"

noncomputable def qExpandAlg (L : Type*) [Field L] (N : ℕ) [NeZero N] :
    LaurentSeries L →ₐ[L] LaurentSeries L :=
  { qExpand L N with
    commutes' := fun c => by
      show qExpand L N (algebraMap L (LaurentSeries L) c) = algebraMap L (LaurentSeries L) c
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

theorem qExpandAlg_apply (L : Type*) [Field L] (N : ℕ) [NeZero N] (f : LaurentSeries L) :
    qExpandAlg L N f = qExpand L N f := rfl

theorem mem_adjoin_qExpand_image_iff (L : Type*) [Field L] (N : ℕ) [NeZero N]
    (K : IntermediateField L (LaurentSeries L)) (x : LaurentSeries L) :
    x ∈ IntermediateField.adjoin L (qExpand L N '' (K : Set (LaurentSeries L))) ↔
      ∃ g : LaurentSeries L, g ∈ K ∧ x = qExpand L N g := by
  have hT : IntermediateField.adjoin L (qExpand L N '' (K : Set (LaurentSeries L))) = K.map (qExpandAlg L N) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro y ⟨g, hg, rfl⟩
      exact (IntermediateField.mem_map _).2 ⟨g, hg, rfl⟩
    · intro y hy
      obtain ⟨g, hg, rfl⟩ := (IntermediateField.mem_map _).1 hy
      exact IntermediateField.subset_adjoin L _ ⟨g, hg, rfl⟩
  rw [hT, IntermediateField.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩

set_option synthInstance.maxHeartbeats 1600000 in

theorem smulCommClass_subgroup (q : ℕ) [Fact q.Prime] (M' : ℕ)
    (G : Subgroup (fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M')) :
    SMulCommClass G (AlgebraicClosure ℚ) (fieldBar q M') :=
  ⟨fun g c y => by
    show (g : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M') • (c • y) =
      c • ((g : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M') • y)
    exact smul_comm _ _ _⟩

end ModularCurve.FullLevel.FixedFieldProof

open ModularCurve.FullLevel.FixedFieldProof in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (x : fieldBar q M')
    (hx : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M' → levelAutBar q M' ζ γ x = x) :
    ∃ g : LaurentSeries (AlgebraicClosure ℚ),
      g ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) ∧
      (x : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) q g := by
  classical

  obtain ⟨G, hGfin, hGmem, hGsurj⟩ := exists_finite_subgroup_forall_levelAutBar_mem q M' hqM' ζ
  haveI : Finite G := hGfin
  have hact : ∀ (g : G) (y : fieldBar q M'),
      g • y = (g : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M') y := fun _ _ => rfl
  haveI hfaith : FaithfulSMul G (fieldBar q M') := ⟨fun {g₁} {g₂} h =>
    Subtype.ext (AlgEquiv.ext fun y => by rw [← hact, ← hact]; exact h y)⟩
  haveI hcomm : SMulCommClass G (AlgebraicClosure ℚ) (fieldBar q M') := smulCommClass_subgroup q M' G
  have hfixG : ∀ y : fieldBar q M', (∀ γ : SL(2, ℤ), γ ∈ Gamma0 M' → levelAutBar q M' ζ γ y = y) →
      ∀ g : G, g • y = y := by
    intro y hy g
    obtain ⟨γ, hγ, hgγ⟩ := hGsurj (g : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M') g.2
    rw [hact, hgγ]
    exact hy γ hγ

  have hcard : Module.finrank (FixedPoints.intermediateField (F := AlgebraicClosure ℚ) (E := fieldBar q M') G)
      (fieldBar q M') = Nat.card G := by
    have := Fintype.ofFinite G
    rw [Nat.card_eq_fintype_card]
    exact FixedPoints.finrank_eq_card G (fieldBar q M')
  obtain ⟨E, hEdef⟩ : ∃ E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)),
      E = IntermediateField.lift
        (FixedPoints.intermediateField (F := AlgebraicClosure ℚ) (E := fieldBar q M') G) := ⟨_, rfl⟩
  have hmemE : ∀ y : fieldBar q M', (∀ g : G, g • y = y) → (y : LaurentSeries (AlgebraicClosure ℚ)) ∈ E := by
    intro y hy
    rw [hEdef, IntermediateField.lift]
    refine (IntermediateField.mem_map _).2 ⟨y, ?_, rfl⟩
    exact (FixedPoints.mem_intermediateField_iff (F := AlgebraicClosure ℚ)).2 hy
  have hEle : E ≤ fieldBar q M' := by rw [hEdef]; exact IntermediateField.lift_le _
  have hErel : E.relfinrank (fieldBar q M') = Nat.card G := by
    have htop : IntermediateField.lift (⊤ : IntermediateField (AlgebraicClosure ℚ) (fieldBar q M')) =
        fieldBar q M' := IntermediateField.lift_top (K := fieldBar q M')
    rw [← hcard, ← IntermediateField.relfinrank_top_right, hEdef]
    convert IntermediateField.relfinrank_map_map
      (A := FixedPoints.intermediateField (F := AlgebraicClosure ℚ) (E := fieldBar q M') G)
      (B := ⊤) (fieldBar q M').val using 2 <;> first | rfl | exact htop.symm | exact Subsingleton.elim _ _

  obtain ⟨hKle, hKpos, hKdeg⟩ := adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three q hq3 M' hqM'
  have hcount := mul_card_ge_of_forall_levelAutBar_mem_of_eq_three q hq3 M' hqM' ζ G hGmem

  have hKE : IntermediateField.adjoin (AlgebraicClosure ℚ)
        (qExpand (AlgebraicClosure ℚ) q ''
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) :
            Set (LaurentSeries (AlgebraicClosure ℚ)))) ≤ E := by
    rw [IntermediateField.adjoin_le_iff]
    rintro y ⟨g, hg, rfl⟩
    have hyF : qExpand (AlgebraicClosure ℚ) q g ∈ fieldBar q M' :=
      hKle (IntermediateField.subset_adjoin (AlgebraicClosure ℚ) _ ⟨g, hg, rfl⟩)
    have := hmemE ⟨qExpand (AlgebraicClosure ℚ) q g, hyF⟩ (hfixG _ (fun γ hγ =>
      levelAutBar_apply_eq_self_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0 q M' hqM' ζ γ hγ g hg _ rfl))
    exact this

  have hmul := IntermediateField.relfinrank_mul_relfinrank hKE hEle
  rw [hErel] at hmul
  have hcpos : 0 < Nat.card G := Nat.card_pos
  have hone : (IntermediateField.adjoin (AlgebraicClosure ℚ)
        (qExpand (AlgebraicClosure ℚ) q ''
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) :
            Set (LaurentSeries (AlgebraicClosure ℚ))))).relfinrank E = 1 := by
    generalize (IntermediateField.adjoin (AlgebraicClosure ℚ)
        (qExpand (AlgebraicClosure ℚ) q ''
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) :
            Set (LaurentSeries (AlgebraicClosure ℚ))))).relfinrank E = r at hmul ⊢
    generalize (IntermediateField.adjoin (AlgebraicClosure ℚ)
        (qExpand (AlgebraicClosure ℚ) q ''
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) :
            Set (LaurentSeries (AlgebraicClosure ℚ))))).relfinrank (fieldBar q M') = R at hmul hKpos hKdeg
    generalize Nat.card G = c at hmul hcpos hcount
    have hRle : R ≤ c := by omega
    have hr1 : r ≤ 1 := by
      have : r * c ≤ 1 * c := by rw [hmul, one_mul]; exact hRle
      exact Nat.le_of_mul_le_mul_right this hcpos
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hmul
      omega
    omega
  have hEK := IntermediateField.relfinrank_eq_one_iff.mp hone

  obtain ⟨g, hg, hxg⟩ :=
    (mem_adjoin_qExpand_image_iff (AlgebraicClosure ℚ) q _ _).1 (hEK (hmemE x (hfixG x hx)))
  exact ⟨g, hg, hxg⟩

end S_ModularCurve_FullLevel_exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq_of_eq_three (solution)
