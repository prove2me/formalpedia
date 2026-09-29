-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c9994edc-a3e7-50f9-8754-3aeae2741dc7

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_LevelOneProlongationPairRegularity
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_levelOneProlongationPair_of_prolongationTuple
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeffEmb_modularUnitSeries_mem_integersSnd_residue_eq_zero
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries
import Theorems.Thm_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries_inv
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isInftySide_cuspInftyBar
import Theorems.Thm_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries_of_neZero
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Theorems.Thm_ModularCurve_geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_divisorLawFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_divisorLawSnd_of_divisorLawFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_cuspLawInfty
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_cuspLawZero_of_cuspLawInfty
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_regularityLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange"
p2m_attr_erase "instance" "ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.tateLaurent_a₆"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one"
p2m_attr_erase "simp" "TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.ModularCurve.PlaceSpecialization"

noncomputable section

namespace Ws19
namespace SHEETREG

section PlaceHelpers
variable {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}

theorem hasValue_add {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem hasValue_neg {g : F} {a : K} (h : v.HasValue g a) : v.HasValue (-g) (-a) := by
  obtain ⟨hg, hr⟩ := h
  refine ⟨neg_mem hg, ?_⟩
  have hx : (⟨-g, neg_mem hg⟩ : v.toValuationSubring) = -⟨g, hg⟩ := rfl
  rw [hx, map_neg, hr, map_neg]

theorem hasValue_sub {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g - g') (a - a') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact hasValue_add h (hasValue_neg h')

theorem ord_pos_of_hasValue_zero {g : F} (h : v.HasValue g 0) (hg : g ≠ 0) : 0 < v.ord g := by
  obtain ⟨hm, hr⟩ := h
  rw [map_zero] at hr
  exact GaussReduction.ord_pos_of_residue_eq_zero v hm hg hr

theorem ord_nonneg_of_mem {g : F} (hm : g ∈ v.toValuationSubring) : 0 ≤ v.ord g := by
  by_cases hg : g = 0
  · rw [hg, Place.ord_zero]
  · exact GaussReduction.ord_nonneg_of_mem_gen v hm hg

end PlaceHelpers

theorem hasValue_of_ord_sub_pos' {K E : Type*} [Field K] [Field E] [Algebra K E] {v : Place K E} {g : E} {c : K}
    (h : 0 < v.ord (g - algebraMap K E c)) : v.HasValue g c := by
  have hne : g - algebraMap K E c ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact lt_irrefl _ h
  have hmem : g - algebraMap K E c ∈ v.toValuationSubring := GaussReduction.mem_of_ord_nonneg_gen v hne h.le
  have hnu : ¬ IsUnit (⟨g - algebraMap K E c, hmem⟩ : v.toValuationSubring) := by
    intro hu
    have h0 := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    have h0' : v.ord (g - algebraMap K E c) = 0 := h0
    rw [h0'] at h; exact lt_irrefl _ h
  have hmax : (⟨g - algebraMap K E c, hmem⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring := by
    rw [mem_maximalIdeal, mem_nonunits_iff]; exact hnu
  have hres0 : residue v.toValuationSubring ⟨g - algebraMap K E c, hmem⟩ = algebraMap K v.ResidueField 0 := by
    rw [map_zero]; exact (residue_eq_zero_iff _).mpr hmax
  have hd := Ws19.SHEETREG.hasValue_add (⟨hmem, hres0⟩ : v.HasValue (g - algebraMap K E c) 0) (v.hasValue_algebraMap c)
  rwa [sub_add_cancel, zero_add] at hd

theorem ramificationIndexAlong_pos' {K E E' : Type*} [Field K] [Field E] [Field E'] [Algebra K E] [Algebra K E']
    (φ : E →ₐ[K] E') (hφ : φ.toRingHom.IsIntegral) (w : Place K E') : 0 < Place.ramificationIndexAlong φ w := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Place.ramificationIndex_pos (F := E) (w := w)

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

local notation "ℚ̄" => AlgebraicClosure ℚ
set_option quotPrecheck false in
local notation "F" => ↥(modularFunctionFieldBar (1 * q))

def U (q : ℕ) [Fact q.Prime] : ↥(modularFunctionFieldBar (1 * q)) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩

theorem coe_U : ((U q : F) : LaurentSeries ℚ̄) = coeffEmb ℚ̄ (modularUnitSeries (1 * q)) := rfl

theorem jFun_def' : (jFun (q := q) : F) = ⟨coeffEmb ℚ̄ jq,
    coeffEmb_mem_laurentBaseChange ℚ̄ (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ := rfl

scoped instance fact_one_mul_prime : Fact (1 * q).Prime := ⟨by rw [Nat.one_mul]; exact Fact.out⟩

theorem modularUnitSeries_level_eq {M K : ℕ} [NeZero M] [NeZero K] (h : M = K) :
    modularUnitSeries M = modularUnitSeries K := by subst h; rfl

theorem coe_U_level : ((U q : F) : LaurentSeries ℚ̄) = coeffEmb ℚ̄ (modularUnitSeries q) := by
  rw [coe_U, modularUnitSeries_level_eq (Nat.one_mul q)]

private theorem _root_.AlgebraicCurve.Place.isRational_of_deg_eq_one' {L E : Type*} [Field L] [Field E]
    [Algebra L E] (v : Place L E) (h : v.deg = 1) : v.IsRational := by
  intro z
  unfold Place.deg at h
  have hbt : (⊥ : Subalgebra L v.ResidueField) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h
  have hz : z ∈ (⊥ : Subalgebra L v.ResidueField) := by rw [hbt]; exact Algebra.mem_top
  exact Algebra.mem_bot.mp hz

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.AlgebraicCurve.Place.isRational_of_deg_eq_one'" "AlgebraicCurve.Place.isRational_of_deg_eq_one'"
theorem isRational_F (W : Place ℚ̄ F) : W.IsRational :=
  W.isRational_of_deg_eq_one' (deg_eq_one_modularFunctionFieldBar (1 * q) W)

theorem jFun_mem_of_not_isCuspidal {W : Place ℚ̄ F} (h : ¬ P.IsCuspidal W) :
    (jFun (q := q) : F) ∈ W.toValuationSubring := by
  simp only [IsCuspidal, not_forall, not_le] at h
  obtain ⟨a, ha⟩ := h
  have hne : (jFun (q := q) : F) - algebraMap ℚ̄ F (a : ℚ̄) ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at ha; exact lt_irrefl _ ha
  have hm := GaussReduction.mem_of_ord_nonneg_gen W hne (le_of_lt ha)
  have := add_mem hm (W.algebraMap_mem' (a : ℚ̄))
  rwa [sub_add_cancel] at this

theorem U_mem_and_inv_mem {W : Place ℚ̄ F} (hj : (jFun (q := q) : F) ∈ W.toValuationSubring) :
    (U q : F) ∈ W.toValuationSubring ∧ (U q : F)⁻¹ ∈ W.toValuationSubring := by

  have key : ∀ (x : LaurentSeries ℚ) (hx : coeffEmb ℚ̄ x ∈ modularFunctionFieldBar (1 * q)),
      IsIntegral (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) x →
      (⟨coeffEmb ℚ̄ x, hx⟩ : F) ∈ W.toValuationSubring := by
    intro x hx hint

    have hsub : ∀ r : LaurentSeries ℚ, r ∈ Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) →
        ∃ hr : coeffEmb ℚ̄ r ∈ modularFunctionFieldBar (1 * q), (⟨coeffEmb ℚ̄ r, hr⟩ : F) ∈ W.toValuationSubring := by
      intro r hr
      refine Algebra.adjoin_induction (hx := hr) ?_ ?_ ?_ ?_
      · intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨_, by simpa [jFun_def'] using hj⟩
      · intro c
        have hcoe : coeffEmb ℚ̄ (algebraMap ℚ (LaurentSeries ℚ) c) = algebraMap ℚ̄ (LaurentSeries ℚ̄) (algebraMap ℚ ℚ̄ c) := by
          rw [algebraMap_laurentSeries_eq_single ℚ c, coeffEmb, coeffMap_single, algebraMap_laurentSeries_eq_single]
        have hmem : coeffEmb ℚ̄ (algebraMap ℚ (LaurentSeries ℚ) c) ∈ modularFunctionFieldBar (1 * q) := by
          rw [hcoe]; exact IntermediateField.algebraMap_mem _ _
        refine ⟨hmem, ?_⟩
        have : (⟨coeffEmb ℚ̄ (algebraMap ℚ (LaurentSeries ℚ) c), hmem⟩ : F) = algebraMap ℚ̄ F (algebraMap ℚ ℚ̄ c) :=
          Subtype.ext hcoe
        rw [this]; exact W.algebraMap_mem' _
      · rintro y z - - ⟨hy, hy'⟩ ⟨hz, hz'⟩
        refine ⟨by rw [map_add]; exact add_mem hy hz, ?_⟩
        have : (⟨coeffEmb ℚ̄ (y + z), by rw [map_add]; exact add_mem hy hz⟩ : F) = ⟨_, hy⟩ + ⟨_, hz⟩ :=
          Subtype.ext (map_add _ _ _)
        rw [this]; exact add_mem hy' hz'
      · rintro y z - - ⟨hy, hy'⟩ ⟨hz, hz'⟩
        refine ⟨by rw [map_mul]; exact mul_mem hy hz, ?_⟩
        have : (⟨coeffEmb ℚ̄ (y * z), by rw [map_mul]; exact mul_mem hy hz⟩ : F) = ⟨_, hy⟩ * ⟨_, hz⟩ :=
          Subtype.ext (map_mul _ _ _)
        rw [this]; exact mul_mem hy' hz'

    obtain ⟨p, hp, hpx⟩ := hint
    let O := W.toValuationSubring

    let θ : Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) →+* O :=
      { toFun := fun r => ⟨⟨coeffEmb ℚ̄ r, (hsub r r.2).1⟩, (hsub r r.2).2⟩
        map_one' := by apply Subtype.ext; apply Subtype.ext; show coeffEmb ℚ̄ 1 = _; rw [map_one]; rfl
        map_mul' := fun a b => by apply Subtype.ext; apply Subtype.ext; show coeffEmb ℚ̄ (a * b) = _; rw [map_mul]; rfl
        map_zero' := by apply Subtype.ext; apply Subtype.ext; show coeffEmb ℚ̄ 0 = _; rw [map_zero]; rfl
        map_add' := fun a b => by apply Subtype.ext; apply Subtype.ext; show coeffEmb ℚ̄ (a + b) = _; rw [map_add]; rfl }
    have hθ : ∀ r, ((θ r : O) : F) = ⟨coeffEmb ℚ̄ r, (hsub r r.2).1⟩ := fun r => rfl

    have hcompeq : (algebraMap F (LaurentSeries ℚ̄)).comp ((algebraMap O F).comp θ)
        = (coeffEmb ℚ̄).comp (algebraMap (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ)) :=
      RingHom.ext (fun r => rfl)
    have hxF : IsIntegral O (⟨coeffEmb ℚ̄ x, hx⟩ : F) := by
      refine ⟨p.map θ, hp.map θ, ?_⟩
      rw [Polynomial.eval₂_map]
      apply (algebraMap F (LaurentSeries ℚ̄)).injective
      rw [map_zero, Polynomial.hom_eval₂, hcompeq,
        show algebraMap F (LaurentSeries ℚ̄) (⟨coeffEmb ℚ̄ x, hx⟩ : F) = coeffEmb ℚ̄ x from rfl,
        ← Polynomial.hom_eval₂, hpx, map_zero]
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := O) (K := F)).mp hxF
    rw [← hy]
    exact y.2
  constructor
  · exact key _ _ (isIntegral_adjoin_jq_modularUnitSeries (1 * q))
  · have hx : coeffEmb ℚ̄ (modularUnitSeries (1 * q))⁻¹ ∈ modularFunctionFieldBar (1 * q) := by
      rw [map_inv₀]; exact inv_mem (U q).2
    have h := key _ hx (isIntegral_adjoin_jq_modularUnitSeries_inv (1 * q))
    have : (⟨coeffEmb ℚ̄ (modularUnitSeries (1 * q))⁻¹, hx⟩ : F) = (U q)⁻¹ := by
      apply Subtype.ext; show coeffEmb ℚ̄ (modularUnitSeries (1 * q))⁻¹ = _
      rw [map_inv₀]; rfl
    rwa [this] at h

section Dict
variable (P)

theorem heckeAlphaBar_jOne :
    heckeAlphaBar ℚ̄ 1 q (⟨coeffEmb ℚ̄ jq, coeffEmb_mem_laurentBaseChange ℚ̄ (modularFunctionField_le_full 1 (jq_mem 1))⟩ :
      modularFunctionFieldBar 1) = (jFun (q := q) : F) :=
  Subtype.ext (by rw [coe_heckeAlphaBar]; rfl)

theorem not_isAffineGeomPlace_reduceFst_of_isCuspidal {W : Place ℚ̄ F} (hW : P.IsCuspidal W) :
    ¬ IsAffineGeomPlace k 1 (P.reduceFst W) := by
  intro haff
  have hpole : (P.reduceFst W).ord (⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) < 0 := by
    apply P.d0_j_pole (W.restrictAlong (heckeAlphaBar ℚ̄ 1 q) hα)
    intro a
    have h := hW a
    have e := Place.ord_restrictAlong (heckeAlphaBar ℚ̄ 1 q) hα W
      ((⟨coeffEmb ℚ̄ jq, coeffEmb_mem_laurentBaseChange ℚ̄ (modularFunctionField_le_full 1 (jq_mem 1))⟩ :
        modularFunctionFieldBar 1) - algebraMap ℚ̄ (modularFunctionFieldBar 1) (a : ℚ̄))
    rw [map_sub, AlgHom.commutes, heckeAlphaBar_jOne] at e
    have hepos := ramificationIndexAlong_pos' (heckeAlphaBar ℚ̄ 1 q) hα W
    by_contra hpos
    push_neg at hpos
    have : 0 < W.ord ((jFun (q := q) : F) - algebraMap ℚ̄ F (a : ℚ̄)) := by
      rw [e]; exact mul_pos (by exact_mod_cast hepos) hpos
    exact absurd h (not_le.mpr this)
  have hmem : (⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) ∈ (P.reduceFst W).toValuationSubring := haff.1
  have := ord_nonneg_of_mem hmem
  omega

end Dict

theorem residue_eq_of_eq {L : Type*} [Field L] {B : ValuationSubring L} {E Ebar : Type*} [Field E] [Algebra L E]
    [Field Ebar] [Algebra (ResidueField B) Ebar]
    {S S' : RegularProlongation B E Ebar} (e : S = S') (x : E) (hx : x ∈ S.integers) (hx' : x ∈ S'.integers) :
    S'.residue ⟨x, hx'⟩ = S.residue ⟨x, hx⟩ := by subst e; rfl

section Tuple
variable (R : ProlongationTuple P)

theorem U_facts :
    ∃ h₁ : (U q : F) ∈ R.R₁.integers, R.R₁.residue ⟨U q, h₁⟩ ≠ 0 ∧
      ((R.R₁.residue ⟨U q, h₁⟩ : modularFunctionFieldFullC (ResidueField A) 1) :
          LaurentSeries (ResidueField A)).order = 1 - (q : ℤ) := by
  obtain ⟨h₁, hne, y, -, -, hord⟩ :=
    R.exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level P (U q) coe_U_level
  exact ⟨h₁, hne, hord⟩

theorem U_mem₁ : (U q : F) ∈ R.R₁.integers := (U_facts R).1
theorem res₁_U_ne : R.R₁.residue ⟨U q, U_mem₁ R⟩ ≠ 0 := (U_facts R).2.1
theorem order_res₁_U : ((R.R₁.residue ⟨U q, U_mem₁ R⟩ : modularFunctionFieldFullC (ResidueField A) 1) :
    LaurentSeries (ResidueField A)).order = 1 - (q : ℤ) := (U_facts R).2.2

theorem U_mem₂_and_res₂ : ∃ h₂ : (U q : F) ∈ R.R₂.integers, R.R₂.residue ⟨U q, h₂⟩ = 0 := by
  obtain ⟨R', -, h2⟩ := exists_levelOneProlongationPair_of_prolongationTuple R
  obtain ⟨hm, hres⟩ := R'.coeffEmb_modularUnitSeries_mem_integersSnd_residue_eq_zero
  have hm' : (U q : F) ∈ R.R₂.integers := h2 ▸ hm
  exact ⟨hm', by rw [residue_eq_of_eq h2 (U q) hm hm']; exact hres⟩

theorem U_mem₂ : (U q : F) ∈ R.R₂.integers := (U_mem₂_and_res₂ R).1
theorem res₂_U : R.R₂.residue ⟨U q, U_mem₂ R⟩ = 0 := (U_mem₂_and_res₂ R).2

theorem U_ne_zero' (R : ProlongationTuple P) : (U q : F) ≠ 0 := by
  intro h
  apply res₁_U_ne R
  have : (⟨U q, U_mem₁ R⟩ : R.R₁.integers) = 0 := Subtype.ext h
  rw [this, map_zero]

theorem red_eq_zero_iff (R : ProlongationTuple P) (c : A) : red c = 0 ↔ c ∈ maximalIdeal A := by
  rw [← R.redBar_residue, map_eq_zero_iff _ (R.redBar).injective, IsLocalRing.residue_eq_zero_iff]

theorem algebraMap_mem₁ (c : A) : algebraMap ℚ̄ F (c : ℚ̄) ∈ R.R₁.integers := (R.R₁.algebraMap_mem_iff _).mpr c.2
theorem algebraMap_mem₂ (c : A) : algebraMap ℚ̄ F (c : ℚ̄) ∈ R.R₂.integers := (R.R₂.algebraMap_mem_iff _).mpr c.2

theorem res₁_algebraMap (c : A) : R.R₁.residue ⟨algebraMap ℚ̄ F (c : ℚ̄), algebraMap_mem₁ R c⟩ =
    algebraMap (ResidueField A) _ (IsLocalRing.residue A c) := R.R₁.residue_algebraMap c
theorem res₂_algebraMap (c : A) : R.R₂.residue ⟨algebraMap ℚ̄ F (c : ℚ̄), algebraMap_mem₂ R c⟩ =
    algebraMap (ResidueField A) _ (IsLocalRing.residue A c) := R.R₂.residue_algebraMap c

theorem ι_algebraMap (c : ResidueField A) :
    R.ι (algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1) c)
      = algebraMap k (modularFunctionFieldC k 1) (R.redBar c) := by
  apply Subtype.ext
  rw [R.ι_coe]
  rw [show ((algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1) c :
      modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
      = algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) c from rfl,
    show ((algebraMap k (modularFunctionFieldC k 1) (R.redBar c) : modularFunctionFieldC k 1) : LaurentSeries k)
      = algebraMap k (LaurentSeries k) (R.redBar c) from rfl,
    algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem residue₁_algebraMap (c : A) :
    R.residue₁ ⟨algebraMap ℚ̄ F (c : ℚ̄), algebraMap_mem₁ R c⟩ = algebraMap k _ (red c) := by
  rw [R.residue₁_apply, res₁_algebraMap, ι_algebraMap, R.redBar_residue]
theorem residue₂_algebraMap (c : A) :
    R.residue₂ ⟨algebraMap ℚ̄ F (c : ℚ̄), algebraMap_mem₂ R c⟩ = algebraMap k _ (red c) := by
  rw [R.residue₂_apply, res₂_algebraMap, ι_algebraMap, R.redBar_residue]

theorem res₁_U_sub_const_ne_zero (t : A) :
    R.R₁.residue ⟨U q - algebraMap ℚ̄ F (t : ℚ̄), sub_mem (U_mem₁ R) (algebraMap_mem₁ R t)⟩ ≠ 0 := by
  intro h
  have hord := order_res₁_U R
  have e : (⟨U q - algebraMap ℚ̄ F (t : ℚ̄), sub_mem (U_mem₁ R) (algebraMap_mem₁ R t)⟩ : R.R₁.integers)
      = ⟨U q, U_mem₁ R⟩ - ⟨_, algebraMap_mem₁ R t⟩ := rfl
  rw [e, map_sub, sub_eq_zero, res₁_algebraMap] at h
  have hq2 : (1 : ℤ) - q < 0 := by have := (Fact.out : q.Prime).two_le; omega
  rw [h, show ((algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A t) :
      modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
        = algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A t) from rfl,
    algebraMap_laurentSeries_eq_single] at hord
  by_cases h0 : IsLocalRing.residue A t = 0
  · rw [h0, map_zero, HahnSeries.order_zero] at hord; omega
  · rw [HahnSeries.order_single h0] at hord; omega

end Tuple

end Ws19.SHEETREG
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.Ws19 P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.Ws19.SHEETREG"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.Ws19"

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.Ws19 P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.Ws19.SHEETREG"

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar jq ModularPolynomialData jq_mem modularFunctionFieldFull modularFunctionField_le_full coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence IsAffineGeomPlace ssJSet frickeInvolutionBar frickeInvolutionFull cuspInftyBar coe_geomAut_coeffEmb modularFunctionFieldFullC modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull isIntegral_adjoin_jq_modularUnitSeries isIntegral_adjoin_jq_modularUnitSeries_inv deg_eq_one_modularFunctionFieldBar isInftySide_cuspInftyBar coe_frickeInvolutionFull_modularUnitSeries_of_neZero frickeInvolutionBar_frickeInvolutionBar geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar"
p2m_open "ModularCurve"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst d0_j_pole LevelOneProlongationPair jFun IsCuspidal redFst exists_levelOneProlongationPair_of_prolongationTuple"
p2m_open "ModularCurve.PlaceSpecialization"
namespace ProlongationTuple
p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "atkinLehnerBar jFun IsCuspidal mem_integers₂_iff residue₁ residue₂ residue₁_apply residue₂_apply OrderLawFixed IsModel RegularityLaw ι_coe R₁ ι redBar_residue R₂ residue₁_eq_modularRedLocHom redBar residue₁_coeffMap residue₂_eq exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level"
p2m_open "ModularCurve.PlaceSpecialization.ProlongationTuple"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

theorem atkinLehnerBar_one_eq_frickeInvolutionBar_s19 (q : ℕ) [Fact q.Prime] :
    ProlongationTuple.atkinLehnerBar 1 q = frickeInvolutionBar (1 * q) :=
  geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar q

private def _root_.ModularCurve.PlaceSpecialization.ProlongationTuple.toLevelOnePairS19 (T : ProlongationTuple P) : LevelOneProlongationPair P where
  redBar := T.redBar
  redBar_residue := T.redBar_residue
  ι := T.ι
  ι_coe := T.ι_coe
  R₁ := T.R₁
  R₂ := T.R₂
  residue₁_coeffMap := T.residue₁_coeffMap
  mem_integers₂_iff := fun f => by
    rw [← atkinLehnerBar_one_eq_frickeInvolutionBar_s19]
    exact T.mem_integers₂_iff f
  residue₂_eq := fun f h => by
    rw [T.residue₂_eq f h]
    congr 1
    apply Subtype.ext
    show ProlongationTuple.atkinLehnerBar 1 q f = frickeInvolutionBar (1 * q) f
    rw [atkinLehnerBar_one_eq_frickeInvolutionBar_s19]
  residue₁_eq_modularRedLocHom := T.residue₁_eq_modularRedLocHom

p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "toLevelOnePairS19"
variable (T : ProlongationTuple P)

@[scoped simp] theorem toLevelOnePairS19_R₁ : T.toLevelOnePairS19.R₁ = T.R₁ := rfl
@[scoped simp] theorem toLevelOnePairS19_R₂ : T.toLevelOnePairS19.R₂ = T.R₂ := rfl
@[scoped simp] theorem toLevelOnePairS19_redBar : T.toLevelOnePairS19.redBar = T.redBar := rfl
@[scoped simp] theorem toLevelOnePairS19_ι : T.toLevelOnePairS19.ι = T.ι := rfl
theorem toLevelOnePairS19_residue₁ : T.toLevelOnePairS19.residue₁ = T.residue₁ := rfl
theorem toLevelOnePairS19_residue₂ : T.toLevelOnePairS19.residue₂ = T.residue₂ := rfl

theorem isModel_toLevelOnePairS19 : T.toLevelOnePairS19.IsModel :=
  ⟨T.toLevelOnePairS19.divisorLawFst,
    T.toLevelOnePairS19.divisorLawSnd_of_divisorLawFst T.toLevelOnePairS19.divisorLawFst,
    T.toLevelOnePairS19.cuspLawInfty,
    T.toLevelOnePairS19.cuspLawZero_of_cuspLawInfty T.toLevelOnePairS19.cuspLawInfty⟩

theorem orderLawFixed_toLevelOnePairS19 : T.toLevelOnePairS19.OrderLawFixed := T.toLevelOnePairS19.orderLawFixed

theorem regularityLaw_toLevelOnePairS19 [IsAlgClosed k] [DecidableEq k] {S₀ : Finset k}
    (hS₀ : ∀ a ∈ S₀, a ∈ ssJSet q k) : T.toLevelOnePairS19.RegularityLaw S₀ :=
  T.toLevelOnePairS19.regularityLaw hS₀

end ProlongationTuple
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.Ws19 P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.Ws19.SHEETREG P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.ModularCurve.PlaceSpecialization.ProlongationTuple"
end PlaceSpecialization
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.Ws19 P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.Ws19.SHEETREG P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.ModularCurve.PlaceSpecialization"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.Ws19 P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.Ws19.SHEETREG P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.ModularCurve"

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne.ModularCurve.PlaceSpecialization"
open Ws19.SHEETREG

set_option maxHeartbeats 16000000 in
theorem solution
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] [DecidableEq k] [IsAlgClosed k]
    {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (R : ProlongationTuple P)
    (u : modularFunctionFieldBar (1 * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (g : modularFunctionFieldBar (1 * q)) (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers)
    (hres₁ : R.R₁.residue ⟨g, h₁⟩ ≠ 0)
    (V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hfix : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V₀))
      = P.reduceFst V₀)
    (haff : IsAffineGeomPlace k 1 (P.reduceFst V₀))
    (hpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
      P.reduceFst W = P.reduceFst V₀ → W ≠ V₀ → 0 ≤ W.ord g)
    (a : A) (ha : red a ≠ 0) (hV₀ : V₀.HasValue (frickeInvolutionBar (1 * q) u) (a : AlgebraicClosure ℚ)) :
    0 ≤ (P.reduceFst V₀).ord (R.residue₁ ⟨g, h₁⟩) := by
  classical
  have huU : u = U q := Subtype.ext (by rw [hu, coe_U_level])
  subst huU
  set v := P.reduceFst V₀ with hvdef
  have hg0 : g ≠ 0 := by
    intro h0; apply hres₁
    rw [show (⟨g, h₁⟩ : R.R₁.integers) = 0 from Subtype.ext h0, map_zero]

  have hAL : ProlongationTuple.atkinLehnerBar 1 q = frickeInvolutionBar (1 * q) :=
    ProlongationTuple.atkinLehnerBar_one_eq_frickeInvolutionBar_s19 q
  obtain ⟨w, hwdef⟩ : ∃ w : ↥(modularFunctionFieldBar (1 * q)), frickeInvolutionBar (1 * q) (U q) = w := ⟨_, rfl⟩
  rw [hwdef] at hV₀
  have hALU : ProlongationTuple.atkinLehnerBar 1 q (U q) = w := by rw [hAL]; exact hwdef
  have hALw : ProlongationTuple.atkinLehnerBar 1 q w = U q := by
    rw [hAL, ← hwdef]; exact frickeInvolutionBar_frickeInvolutionBar _ _
  have hw₁ : w ∈ R.R₁.integers := by
    have := (R.mem_integers₂_iff (U q)).mp (U_mem₂ R); rwa [hALU] at this
  have hresw₁ : R.R₁.residue ⟨w, hw₁⟩ = 0 := by
    have e := R.residue₂_eq (U q) (U_mem₂ R)
    rw [res₂_U] at e
    refine (e.trans ?_).symm
    congr 1
    exact Subtype.ext hALU
  have hw₂ : w ∈ R.R₂.integers := (R.mem_integers₂_iff w).mpr (by rw [hALw]; exact U_mem₁ R)

  have hwU : w = algebraMap (AlgebraicClosure ℚ) _ (algebraMap ℚ (AlgebraicClosure ℚ) (((1 * q : ℕ) : ℚ) ^ 12)) * (U q)⁻¹ := by
    apply Subtype.ext
    have h1 := coe_geomAut_coeffEmb (AlgebraicClosure ℚ) (modularFunctionFieldFull (1 * q)) (frickeInvolutionFull (1 * q))
      ⟨modularUnitSeries (1 * q), modularUnitSeries_mem_modularFunctionFieldFull (1 * q)⟩
    have h2 := coe_frickeInvolutionFull_modularUnitSeries_of_neZero (1 * q)
      (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))
    rw [h2, ← HahnSeries.C_mul_eq_smul, map_mul, map_inv₀] at h1
    rw [← hwdef]
    refine h1.trans ?_
    have hc : coeffEmb (AlgebraicClosure ℚ) (HahnSeries.C (((1 * q : ℕ) : ℚ) ^ 12))
        = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))
            (algebraMap ℚ (AlgebraicClosure ℚ) (((1 * q : ℕ) : ℚ) ^ 12)) := by
      rw [HahnSeries.C_apply, coeffEmb, coeffMap_single, algebraMap_laurentSeries_eq_single]
    rw [hc]
    rfl

  have hca₁ := algebraMap_mem₁ R a
  have hca₂ := algebraMap_mem₂ R a
  have hd₁ : w - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) ∈ R.R₁.integers := sub_mem hw₁ hca₁
  have hd₂ : w - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) ∈ R.R₂.integers := sub_mem hw₂ hca₂
  have hresa : IsLocalRing.residue A a ≠ 0 := by
    intro h0; apply ha
    rw [red_eq_zero_iff R]; exact (IsLocalRing.residue_eq_zero_iff _).mp h0
  have hinj : Function.Injective (algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1)) :=
    (algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1)).injective
  have hresd₁ : R.R₁.residue ⟨_, hd₁⟩ = -algebraMap (ResidueField A) _ (IsLocalRing.residue A a) := by
    have e : (⟨_, hd₁⟩ : R.R₁.integers) = ⟨w, hw₁⟩ - ⟨_, hca₁⟩ := rfl
    rw [e, map_sub, hresw₁, res₁_algebraMap, zero_sub]
  have hresd₁ne : R.R₁.residue ⟨_, hd₁⟩ ≠ 0 := by
    rw [hresd₁, neg_ne_zero]; exact (map_ne_zero_iff _ hinj).mpr hresa
  have hd0 : w - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0; apply hresd₁ne
    rw [show (⟨_, hd₁⟩ : R.R₁.integers) = 0 from Subtype.ext h0, map_zero]
  have hdval : V₀.HasValue (w - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ)) 0 := by
    have := hasValue_sub hV₀ (V₀.hasValue_algebraMap (a : AlgebraicClosure ℚ))
    rwa [sub_self] at this
  have hdord : 0 < V₀.ord (w - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ)) :=
    ord_pos_of_hasValue_zero hdval hd0
  have hdW : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)), P.reduceFst W = v →
      0 ≤ W.ord (w - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ)) := by
    intro W hW
    have hnc : ¬ P.IsCuspidal W := fun hc =>
      (not_isAffineGeomPlace_reduceFst_of_isCuspidal P hc) (hW ▸ haff)
    have hU := (U_mem_and_inv_mem (jFun_mem_of_not_isCuspidal hnc)).2
    have hwW : w ∈ W.toValuationSubring := by
      rw [hwU]; exact mul_mem (W.algebraMap_mem' _) hU
    exact ord_nonneg_of_mem (sub_mem hwW (W.algebraMap_mem' _))

  set n : ℕ := (-(V₀.ord g)).toNat with hndef
  have hn : 0 ≤ V₀.ord g + n := by
    have := Int.self_le_toNat (-(V₀.ord g)); omega
  set d : ↥(modularFunctionFieldBar (1 * q)) := w - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) with hddef
  set H : ↥(modularFunctionFieldBar (1 * q)) := g * d ^ n with hHdef
  have hH₁ : H ∈ R.R₁.integers := mul_mem h₁ (pow_mem hd₁ n)
  have hH₂ : H ∈ R.R₂.integers := mul_mem h₂ (pow_mem hd₂ n)
  have hresH₁ : R.R₁.residue ⟨H, hH₁⟩ = R.R₁.residue ⟨g, h₁⟩ * R.R₁.residue ⟨_, hd₁⟩ ^ n := by
    have e : (⟨H, hH₁⟩ : R.R₁.integers) = ⟨g, h₁⟩ * ⟨_, hd₁⟩ ^ n := by
      apply Subtype.ext
      simp only [hHdef, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    rw [e, map_mul, map_pow]
  have hresH₁ne : R.R₁.residue ⟨H, hH₁⟩ ≠ 0 := by
    rw [hresH₁]; exact mul_ne_zero hres₁ (pow_ne_zero _ hresd₁ne)
  have hHreg : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)), P.redFst W = v → 0 ≤ W.ord H := by
    intro W hW
    change P.reduceFst W = v at hW
    rw [hHdef, W.ord_mul hg0 (pow_ne_zero _ hd0), ← zpow_natCast, W.ord_zpow]
    by_cases hWV : W = V₀
    · subst hWV
      nlinarith [hdord, hn]
    · have h1 := hpole W hW hWV
      have h2 := hdW W hW
      positivity
  have hvc : v ≠ P.redFst (cuspInftyBar (1 * q)) := by
    intro hvc
    have hcusp : P.IsCuspidal (cuspInftyBar (1 * q)) := (ModularCurve.isInftySide_cuspInftyBar P).1
    apply not_isAffineGeomPlace_reduceFst_of_isCuspidal P hcusp
    change IsAffineGeomPlace k 1 (P.redFst (cuspInftyBar (1 * q)))
    rw [← hvc]; exact haff
  have hRL := (R.toLevelOnePairS19.regularityLaw (S₀ := (∅ : Finset k)) (by simp)).1 H hH₁ hH₂ v hfix hvc hHreg
  have hresH₁ne' : R.residue₁ ⟨H, hH₁⟩ ≠ 0 := by
    rw [R.residue₁_apply]; exact (map_ne_zero_iff _ R.ι.injective).mpr hresH₁ne
  have hkey : 0 ≤ v.ord (R.residue₁ ⟨H, hH₁⟩) := by
    have := hRL.1
    rw [ProlongationTuple.toLevelOnePairS19_residue₁] at this
    exact this hresH₁ne'
  have hres₁H : R.residue₁ ⟨H, hH₁⟩ = R.residue₁ ⟨g, h₁⟩ * (algebraMap k _ (-(red a))) ^ n := by
    rw [R.residue₁_apply, hresH₁, map_mul, map_pow, ← R.residue₁_apply, hresd₁, map_neg, map_neg,
      ← res₁_algebraMap R a, ← R.residue₁_apply, residue₁_algebraMap]
  have hc0 : (algebraMap k (modularFunctionFieldC k 1) (-(red a))) ≠ 0 := by
    rw [map_ne_zero_iff _ (algebraMap k (modularFunctionFieldC k 1)).injective]; exact neg_ne_zero.mpr ha
  have hg₁0 : R.residue₁ ⟨g, h₁⟩ ≠ 0 := by
    rw [R.residue₁_apply]; exact (map_ne_zero_iff _ R.ι.injective).mpr hres₁
  rw [hres₁H, v.ord_mul hg₁0 (pow_ne_zero _ hc0), ← zpow_natCast, v.ord_zpow,
    (v.hasValue_algebraMap (-(red a))).ord_eq_zero (neg_ne_zero.mpr ha)] at hkey
  simpa using hkey

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne (solution)
