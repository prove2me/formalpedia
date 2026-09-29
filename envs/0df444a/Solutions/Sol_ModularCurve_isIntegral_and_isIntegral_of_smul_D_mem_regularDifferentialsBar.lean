-- Prove2me | solution 1 for ModularCurve.isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentialsBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/6348e099-ea0b-55cf-8e23-934c6f8195d1

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_ord_jBar_sub_eq_one_of_ne_zero_of_ne
import Theorems.Thm_ModularCurve_ord_jBar_dvd_three
import Theorems.Thm_ModularCurve_ord_jBar_sub_1728_dvd_two
import Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_D_eq_ord_sub_one
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_smul_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_ModularCurve_sum_neg_ord_jBar_eq_dedekindPsi
import Theorems.Thm_AlgebraicCurve_regularDiffs_eq_regularDifferentials
import Theorems.Thm_AlgebraicCurve_mem_regularDiffs_iff
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentialsBar
p2m_attr_erase "instance" "ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "simp" "ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AddMonoid.End.DualEndData.symm_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero"

open ModularCurve AlgebraicCurve HahnSeries KaehlerDifferential

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

namespace ALGGlue

variable (N : ℕ) [NeZero N]

local notation "𝕂" => AlgebraicClosure ℚ
local notation "𝔽" => ModularCurve.modularFunctionFieldBar N

abbrev jB : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩

theorem D_jB_ne_zero : D 𝕂 𝔽 (jB N) ≠ 0 := by
  intro h
  have h1 : diffQExp 𝔽 (D 𝕂 𝔽 (jB N)) = qEuler 𝕂 ((jB N : 𝔽) : LaurentSeries 𝕂) := diffQExp_D _ _
  rw [h, map_zero] at h1
  have h2 := congrArg (fun s : LaurentSeries 𝕂 => s.coeff (-1)) h1
  simp only at h2
  rw [qEuler_coeff] at h2
  have h3 : ((jB N : 𝔽) : LaurentSeries 𝕂).coeff (-1) = 1 := by
    show (coeffEmb 𝕂 jq).coeff (-1) = 1
    rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]
  rw [h3, HahnSeries.coeff_zero] at h2
  norm_num at h2

theorem jB_ne_zero : (jB N : 𝔽) ≠ 0 := by
  intro h
  have := D_jB_ne_zero N
  rw [h, map_zero] at this
  exact this rfl

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_pow' (v : Place K F) (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  have := v.ord_zpow f (n : ℤ)
  rwa [zpow_natCast] at this

theorem ord_algebraMap (v : Place K F) {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have h1 : 0 ≤ v.ord (algebraMap K F c) := v.ord_nonneg_of_mem (v.algebraMap_mem' c)
  have h2 : 0 ≤ v.ord (algebraMap K F c⁻¹) := v.ord_nonneg_of_mem (v.algebraMap_mem' c⁻¹)
  rw [map_inv₀, v.ord_inv] at h2
  omega

theorem ord_neg (v : Place K F) (f : F) : v.ord (-f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have h1 : v.ord (-f) = v.ord (-1) + v.ord f := by
    rw [← v.ord_mul (by norm_num) hf, neg_one_mul]
  have h2 : v.ord ((-1 : F)) = 0 := by
    have := v.ord_zpow (-1 : F) 2
    norm_num at this
    linarith
  rw [h1, h2, zero_add]

theorem ord_pos_of_mem_maximalIdeal (v : Place K F) {a : v.toValuationSubring}
    (ha : a ∈ IsLocalRing.maximalIdeal v.toValuationSubring) (ha0 : (a : F) ≠ 0) : 0 < v.ord (a : F) := by
  by_contra hle
  push Not at hle
  have h0 : 0 ≤ v.ord (a : F) := v.ord_nonneg_of_mem a.2
  have heq : v.ord (a : F) = 0 := le_antisymm hle h0
  have hinv : (a : F)⁻¹ ∈ v.toValuationSubring := by
    rw [v.mem_iff_ord_nonneg (inv_ne_zero ha0), v.ord_inv, heq, neg_zero]
  have hunit : IsUnit a := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨(a : F)⁻¹, hinv⟩, ?_⟩
    ext
    simp [mul_inv_cancel₀ ha0]
  exact (IsLocalRing.mem_maximalIdeal _).mp ha hunit

theorem exists_value [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    ∃ c : K, f - algebraMap K F c = 0 ∨ 0 < v.ord (f - algebraMap K F c) := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨c, hc⟩ := hbij.2 (IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩)
  refine ⟨c, ?_⟩
  have hmem : (⟨f, hf⟩ - algebraMap K v.toValuationSubring c : v.toValuationSubring) ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc]
    rw [IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField]
    exact sub_self _
  have hcoe : ((⟨f, hf⟩ - algebraMap K v.toValuationSubring c : v.toValuationSubring) : F) =
      f - algebraMap K F c := by
    push_cast
    rw [v.coe_algebraMap]
  by_cases h0 : f - algebraMap K F c = 0
  · exact Or.inl h0
  · right
    have := ord_pos_of_mem_maximalIdeal v hmem (by rw [hcoe]; exact h0)
    rwa [hcoe] at this

end Generic

theorem ord_bound (x : 𝔽) (hx0 : x ≠ 0) (hreg : ∀ v : Place 𝕂 𝔽, 0 ≤ v.ordDiff (x • D 𝕂 𝔽 (jB N)))
    [FiniteDimensional (IntermediateField.adjoin 𝕂 ({(jB N : 𝔽)} : Set 𝔽)) 𝔽]
    (v : Place 𝕂 𝔽) {g : 𝔽} (hg : v.ord g ≠ 0) (hDg : D 𝕂 𝔽 g = D 𝕂 𝔽 (jB N)) :
    1 - v.ord g ≤ v.ord x := by
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin 𝕂 ({(jB N : 𝔽)} : Set 𝔽)) 𝔽 :=
    Algebra.IsAlgebraic.of_finite _ _
  have h := hreg v
  rw [← hDg] at h
  rw [Place.ordDiff_smul_of_perfectField (jB N : 𝔽) v hx0 (by rw [hDg]; exact D_jB_ne_zero N),
    Place.ordDiff_D_eq_ord_sub_one (jB N : 𝔽) v hg] at h
  omega

theorem main (x : 𝔽) (hx : x • D 𝕂 𝔽 (jB N) ∈ regularDifferentialsBar N) :
    IsIntegral (Algebra.adjoin 𝕂 ({(jB N : 𝔽)} : Set 𝔽)) (x ^ 6 * (jB N) ^ 4 * (jB N - algebraMap 𝕂 𝔽 1728) ^ 3) ∧
    IsIntegral (Algebra.adjoin 𝕂 ({(jB N : 𝔽)⁻¹} : Set 𝔽))
      (x ^ (2 * dedekindPsi N) * (jB N) ^ (dedekindPsi N + 1) * (jB N - algebraMap 𝕂 𝔽 1728) ^ dedekindPsi N) := by
  classical
  haveI hCO := ModularCurve.isCurveOver_modularFunctionFieldBar N
  haveI hEFT := ModularCurve.essFiniteType_modularFunctionFieldBar N
  haveI hFD : FiniteDimensional (IntermediateField.adjoin 𝕂 ({(jB N : 𝔽)} : Set 𝔽)) 𝔽 :=
    ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_of_neZero N
  haveI hALG : Algebra.IsAlgebraic (IntermediateField.adjoin 𝕂 ({(jB N : 𝔽)} : Set 𝔽)) 𝔽 :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI hPD : HasPrincipalDivisors 𝕂 𝔽 := IsCurveOver.hasPrincipalDivisors
  set J : 𝔽 := jB N with hJdef
  set ψ : ℕ := dedekindPsi N with hψdef
  have hψpos : 0 < ψ := ModularCurve.dedekindPsi_pos N (NeZero.ne N)
  have hJ0 : J ≠ 0 := jB_ne_zero N

  by_cases hx0 : x = 0
  · subst hx0
    refine ⟨?_, ?_⟩
    · rw [zero_pow (by norm_num), zero_mul, zero_mul]; exact isIntegral_zero
    · rw [zero_pow (by omega), zero_mul, zero_mul]; exact isIntegral_zero

  have hreg : ∀ v : Place 𝕂 𝔽, 0 ≤ v.ordDiff (x • D 𝕂 𝔽 J) := by
    have h1 : x • D 𝕂 𝔽 J ∈ regularDiffs 𝕂 𝔽 := by
      rw [AlgebraicCurve.regularDiffs_eq_regularDifferentials]; exact hx
    exact (AlgebraicCurve.mem_regularDiffs_iff (J : 𝔽) _).mp h1

  obtain ⟨Dv, hDv, -⟩ := HasPrincipalDivisors.exists_divisor (K := 𝕂) (F := 𝔽) J hJ0
  let S : Finset (Place 𝕂 𝔽) := Dv.support.filter (fun v => v.ord J < 0)
  have hS : ∀ v, v ∈ S ↔ v.ord J < 0 := by
    intro v
    simp only [S, Finset.mem_filter, Finsupp.mem_support_iff, and_iff_right_iff_imp]
    intro hv
    rw [hDv v]
    exact hv.ne
  have hsum : ∑ v ∈ S, -v.ord J = (ψ : ℤ) := by
    have := ModularCurve.sum_neg_ord_jBar_eq_dedekindPsi N S hS
    exact_mod_cast this
  have hwidth : ∀ v : Place 𝕂 𝔽, v.ord J < 0 → -v.ord J ≤ (ψ : ℤ) := by
    intro v hv
    rw [← hsum]
    exact Finset.single_le_sum (f := fun w => -w.ord J)
      (fun w hw => by have := (hS w).mp hw; show (0 : ℤ) ≤ -w.ord J; omega) ((hS v).mpr hv)
  have hpole : ∃ v₀ : Place 𝕂 𝔽, v₀.ord J < 0 := by
    by_contra hno
    push Not at hno
    have hSe : S = ∅ := by
      ext v
      simp only [Finset.notMem_empty, iff_false]
      intro hv
      exact absurd ((hS v).mp hv) (not_lt.mpr (hno v))
    rw [hSe, Finset.sum_empty] at hsum
    have h' : (ψ : ℤ) = 0 := hsum.symm
    omega
  obtain ⟨v₀, hv₀⟩ := hpole

  have htr : Transcendental 𝕂 J := by
    intro halg
    have hint : IsIntegral 𝕂 J := halg.isIntegral
    have hint' : IsIntegral v₀.toValuationSubring J := hint.tower_top
    have hmem : J ∈ v₀.toValuationSubring := by
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := v₀.toValuationSubring) (K := 𝔽)).mp hint'
      rw [← hy]
      exact y.2
    have := v₀.ord_nonneg_of_mem hmem
    omega
  have hJne1728 : J - algebraMap 𝕂 𝔽 1728 ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    have := ord_algebraMap v₀ (c := (1728 : 𝕂)) (by norm_num)
    rw [← h] at this
    omega

  have h1728_0 : v₀.ord (algebraMap 𝕂 𝔽 1728) = 0 := ord_algebraMap v₀ (by norm_num)
  have hordJsub_of_pos : ∀ v : Place 𝕂 𝔽, 0 < v.ord J → v.ord (J - algebraMap 𝕂 𝔽 1728) = 0 := by
    intro v hv
    have hc : v.ord (-(algebraMap 𝕂 𝔽 1728)) = 0 := by rw [ord_neg]; exact ord_algebraMap v (by norm_num)
    have := v.ord_add_eq_of_lt (f := -(algebraMap 𝕂 𝔽 1728)) (g := J)
      (neg_ne_zero.mpr (by rw [Ne, map_eq_zero]; norm_num)) hJ0 (by rw [hc]; exact hv)
    rw [hc] at this
    rwa [sub_eq_add_neg, add_comm]
  have hordJsub_of_neg : ∀ v : Place 𝕂 𝔽, v.ord J < 0 → v.ord (J - algebraMap 𝕂 𝔽 1728) = v.ord J := by
    intro v hv
    have hc : v.ord (-(algebraMap 𝕂 𝔽 1728)) = 0 := by rw [ord_neg]; exact ord_algebraMap v (by norm_num)
    have := v.ord_add_eq_of_lt (f := J) (g := -(algebraMap 𝕂 𝔽 1728)) hJ0
      (neg_ne_zero.mpr (by rw [Ne, map_eq_zero]; norm_num)) (by rw [hc]; exact hv)
    rwa [← sub_eq_add_neg] at this
  have hordJ_of_sub_pos : ∀ (v : Place 𝕂 𝔽) (c : 𝕂), c ≠ 0 → 0 < v.ord (J - algebraMap 𝕂 𝔽 c) →
      v.ord J = 0 := by
    intro v c hc hv
    have h1 : v.ord (algebraMap 𝕂 𝔽 c) = 0 := ord_algebraMap v hc
    have hne : J - algebraMap 𝕂 𝔽 c ≠ 0 := by
      intro h; rw [h, v.ord_zero] at hv; exact lt_irrefl _ hv
    have := v.ord_add_eq_of_lt (f := algebraMap 𝕂 𝔽 c) (g := J - algebraMap 𝕂 𝔽 c)
      (by rw [Ne, map_eq_zero]; exact hc) hne (by rw [h1]; exact hv)
    rw [h1, add_sub_cancel] at this
    exact this

  have hDsub : ∀ c : 𝕂, D 𝕂 𝔽 (J - algebraMap 𝕂 𝔽 c) = D 𝕂 𝔽 J := by
    intro c
    rw [map_sub, Derivation.map_algebraMap, sub_zero]

  have hfinite : ∀ v : Place 𝕂 𝔽, v.ord J = 0 →
      (0 ≤ v.ord x ∧ v.ord (J - algebraMap 𝕂 𝔽 1728) = 0) ∨
      (∃ a : ℤ, 0 < a ∧ a ≤ 2 ∧ v.ord (J - algebraMap 𝕂 𝔽 1728) = a ∧ 1 - a ≤ v.ord x) := by
    intro v hvJ
    have hJmem : J ∈ v.toValuationSubring := by rw [v.mem_iff_ord_nonneg hJ0, hvJ]
    obtain ⟨c, hc⟩ := exists_value v hJmem
    have hcpos : 0 < v.ord (J - algebraMap 𝕂 𝔽 c) := by
      rcases hc with hc | hc
      · exfalso
        rw [sub_eq_zero] at hc
        have := ord_algebraMap v₀ (c := c) (by rintro rfl; rw [map_zero] at hc; exact hJ0 hc)
        rw [← hc] at this
        omega
      · exact hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero, sub_zero] at hcpos
      omega
    by_cases hc1728 : c = 1728
    · subst hc1728
      right
      refine ⟨v.ord (J - algebraMap 𝕂 𝔽 1728), hcpos, ?_, rfl, ?_⟩
      · have hd := ModularCurve.ord_jBar_sub_1728_dvd_two N v hcpos
        exact Int.le_of_dvd (by norm_num) hd
      · exact ord_bound N x hx0 hreg v hcpos.ne' (hDsub 1728)
    · left
      have h1 : v.ord (J - algebraMap 𝕂 𝔽 c) = 1 :=
        ModularCurve.ord_jBar_sub_eq_one_of_ne_zero_of_ne N v c hc0 hc1728 hcpos
      have hb := ord_bound N x hx0 hreg v (g := J - algebraMap 𝕂 𝔽 c) (by rw [h1]; norm_num) (hDsub c)
      rw [h1] at hb
      refine ⟨by omega, ?_⟩

      have hcc : v.ord (algebraMap 𝕂 𝔽 (c - 1728)) = 0 := ord_algebraMap v (sub_ne_zero.mpr hc1728)
      have := v.ord_add_eq_of_lt (f := algebraMap 𝕂 𝔽 (c - 1728)) (g := J - algebraMap 𝕂 𝔽 c)
        (by rw [Ne, map_eq_zero]; exact sub_ne_zero.mpr hc1728)
        (by intro h; rw [h, v.ord_zero] at hcpos; exact lt_irrefl _ hcpos) (by rw [hcc]; exact hcpos)
      rw [hcc] at this
      rw [← this, map_sub]
      congr 1
      ring
  refine ⟨?_, ?_⟩
  ·
    refine AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg (K := 𝕂) (F := 𝔽) J htr _ ?_
    intro v hvJ
    have hne : x ^ 6 * J ^ 4 * (J - algebraMap 𝕂 𝔽 1728) ^ 3 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0)) (pow_ne_zero _ hJne1728)
    rw [v.ord_mul (mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0)) (pow_ne_zero _ hJne1728),
      v.ord_mul (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0), ord_pow', ord_pow', ord_pow']
    rcases hvJ.lt_or_eq with hpos | hzero
    ·
      have hd := ModularCurve.ord_jBar_dvd_three N v hpos
      have ha3 : v.ord J ≤ 3 := Int.le_of_dvd (by norm_num) hd
      have hb := ord_bound N x hx0 hreg v hpos.ne' rfl
      rw [hordJsub_of_pos v hpos]
      push_cast
      nlinarith
    · rcases hfinite v hzero.symm with ⟨hx', h1728'⟩ | ⟨a, ha0, ha2, h1728', hb⟩
      · rw [← hzero, h1728']; push_cast; nlinarith
      · rw [← hzero, h1728']; push_cast; nlinarith
  ·
    have htr' : Transcendental 𝕂 J⁻¹ := by
      intro halg
      exact htr (by simpa using halg.inv)
    have hadj : IntermediateField.adjoin 𝕂 ({J⁻¹} : Set 𝔽) = IntermediateField.adjoin 𝕂 ({J} : Set 𝔽) := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_simple_le_iff]
        exact inv_mem (IntermediateField.mem_adjoin_simple_self 𝕂 J)
      · rw [IntermediateField.adjoin_simple_le_iff]
        have h1 := IntermediateField.mem_adjoin_simple_self 𝕂 (J⁻¹)
        have h2 : (J⁻¹)⁻¹ ∈ IntermediateField.adjoin 𝕂 ({J⁻¹} : Set 𝔽) := inv_mem h1
        rwa [inv_inv] at h2
    haveI : FiniteDimensional (IntermediateField.adjoin 𝕂 ({J⁻¹} : Set 𝔽)) 𝔽 := by
      rw [hadj]; exact hFD
    refine AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg (K := 𝕂) (F := 𝔽) J⁻¹ htr' _ ?_
    intro v hvJinv
    rw [v.ord_inv] at hvJinv
    have hvJ : v.ord J ≤ 0 := by omega
    rw [v.ord_mul (mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0)) (pow_ne_zero _ hJne1728),
      v.ord_mul (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0), ord_pow', ord_pow', ord_pow']
    rcases hvJ.lt_or_eq with hneg | hzero
    ·
      have hw := hwidth v hneg
      have hb := ord_bound N x hx0 hreg v hneg.ne rfl
      rw [hordJsub_of_neg v hneg]
      push_cast
      nlinarith
    · rcases hfinite v hzero with ⟨hx', h1728'⟩ | ⟨a, ha0, ha2, h1728', hb⟩
      · rw [hzero, h1728']; push_cast; nlinarith
      · rw [hzero, h1728']; push_cast; nlinarith

end ALGGlue

theorem solution (N : ℕ) [NeZero N]
    (x : ModularCurve.modularFunctionFieldBar N)
    (hx : x • KaehlerDifferential.D (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N)
        (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq, ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩ : ModularCurve.modularFunctionFieldBar N) ∈ ModularCurve.regularDifferentialsBar N) :
    IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({(⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq, ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩ : ModularCurve.modularFunctionFieldBar N)} : Set (ModularCurve.modularFunctionFieldBar N)))
        (x ^ 6 * (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq, ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩ : ModularCurve.modularFunctionFieldBar N) ^ 4 * ((⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq, ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩ : ModularCurve.modularFunctionFieldBar N) - algebraMap (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) 1728) ^ 3) ∧
      IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({(⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq, ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩ : ModularCurve.modularFunctionFieldBar N)⁻¹} : Set (ModularCurve.modularFunctionFieldBar N)))
        (x ^ (2 * ModularCurve.dedekindPsi N) * (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq, ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩ : ModularCurve.modularFunctionFieldBar N) ^ (ModularCurve.dedekindPsi N + 1) *
          ((⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq, ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩ : ModularCurve.modularFunctionFieldBar N) - algebraMap (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) 1728) ^ ModularCurve.dedekindPsi N) :=
  ALGGlue.main N x hx

end

end S_ModularCurve_isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentialsBar
end P2MW
export P2MW.S_ModularCurve_isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentialsBar (solution)
