-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.le_ord_residue_and_exists_hasValue_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/3ecd0e84-032e-5c2f-81d9-15fbc09e858d

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_exists_hasValue_frobNodePair_of_forall_pole_not_centred
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersFst_iff_coe_mem_modularLocalized
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersSnd_iff_coe_frickeInvolutionBar_mem_modularLocalized
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_le_ord_residue_and_exists_hasValue_of_mul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

set_option autoImplicit false

namespace FltWs24
namespace N3

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ord_charLGeomPlaceOfPoint_jqModC_sub (k : Type*) [Field k] (b : k) :
    (charLGeomPlaceOfPoint k b).ord
      ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) b) = 1 := by

  set e : RatFunc k ≃+* ↥(modularFunctionFieldC k 1) := (ratFuncEquivCharLOneC k).toRingEquiv with he_def
  have he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k ↥(modularFunctionFieldC k 1) c :=
    fun c => (ratFuncEquivCharLOneC k).commutes c
  have hplace : charLGeomPlaceOfPoint k b = Place.congrRingEquiv e he (RationalFunctionField.placeOfPoint k b) := rfl
  have hX : e RatFunc.X = (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) := by
    apply Subtype.ext
    rw [he_def]
    show ((ratFuncEquivCharLOneC k RatFunc.X : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = jqModC k
    unfold ratFuncEquivCharLOneC
    rw [AlgEquiv.trans_apply]
    first
      | exact RatFunc.algEquivOfTranscendental_X (jqModC k) (transcendental_jqModC k)
      | (rw [IntermediateField.equivOfEq_apply]
         exact RatFunc.algEquivOfTranscendental_X (jqModC k) (transcendental_jqModC k))
      | (rw [← RatFunc.algEquivOfTranscendental_X (jqModC k) (transcendental_jqModC k)]
         rfl)
  have helem : (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) b
      = e (algebraMap (Polynomial k) (RatFunc k) (Polynomial.X - Polynomial.C b)) := by
    rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_sub, hX, ← he b, RatFunc.algebraMap_eq_C]
  rw [hplace, helem, Place.ord_congrRingEquiv,
    RationalFunctionField.ord_placeOfPoint_algebraMap b (Polynomial.X_sub_C_ne_zero b),
    Polynomial.rootMultiplicity_X_sub_C_self]
  simp

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

theorem hasValue_of_mul {v : Place k ↥(modularFunctionFieldC k 1)} {x u : ↥(modularFunctionFieldC k 1)} {c₀ l : k}
    (hu : v.HasValue u l) (hl : l ≠ 0) (hxu : v.HasValue (x * u) c₀) : v.HasValue x (c₀ * l⁻¹) := by
  have hu0 : u ≠ 0 := hu.ne_zero hl
  have : x = (x * u) * u⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hu0, mul_one]
  rw [this]
  exact hxu.mul (hu.inv hl)

theorem main {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
    (f t : ↥(modularFunctionFieldBar (1 * q)))
    (hf₁ : f ∈ R.R₁.integers) (hf₂ : f ∈ R.R₂.integers) (ht₁ : t ∈ R.R₁.integers) (ht₂ : t ∈ R.R₂.integers)
    (hpole : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → 0 ≤ W.ord (f * t))
    (n₁ n₂ : ℤ) (l₁ l₂ : k) (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (htw₁ : (frobNodePair q a).1.HasValue
      (((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) a) ^ (-n₁)
        * (R.residue₁ ⟨t, ht₁⟩ : ↥(modularFunctionFieldC k 1))) l₁)
    (htw₂ : (frobNodePair q a).2.HasValue
      (((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) (a ^ q)) ^ (-n₂)
        * (R.residue₂ ⟨t, ht₂⟩ : ↥(modularFunctionFieldC k 1))) l₂) :
    (R.residue₁ ⟨f, hf₁⟩ ≠ 0 → -n₁ ≤ (frobNodePair q a).1.ord (R.residue₁ ⟨f, hf₁⟩ : ↥(modularFunctionFieldC k 1))) ∧
    (R.residue₂ ⟨f, hf₂⟩ ≠ 0 → -n₂ ≤ (frobNodePair q a).2.ord (R.residue₂ ⟨f, hf₂⟩ : ↥(modularFunctionFieldC k 1))) ∧
    ∃ c : k,
      (frobNodePair q a).1.HasValue
        (((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) a) ^ n₁
          * (R.residue₁ ⟨f, hf₁⟩ : ↥(modularFunctionFieldC k 1))) (l₂ * c) ∧
      (frobNodePair q a).2.HasValue
        (((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) (a ^ q)) ^ n₂
          * (R.residue₂ ⟨f, hf₂⟩ : ↥(modularFunctionFieldC k 1))) (l₁ * c) := by
  haveI : NeZero (1 * q) := ⟨by rw [one_mul]; exact (Fact.out : q.Prime).ne_zero⟩

  have hg₁ : f * t ∈ R.R₁.integers := mul_mem hf₁ ht₁
  have hg₂ : f * t ∈ R.R₂.integers := mul_mem hf₂ ht₂
  have hg₁' := (LevelOneProlongationPair.mem_integersFst_iff_coe_mem_modularLocalized R (f * t)).mp hg₁
  have hg₂' := (LevelOneProlongationPair.mem_integersSnd_iff_coe_frickeInvolutionBar_mem_modularLocalized R (f * t)).mp hg₂
  obtain ⟨k₁, hk₁⟩ := R.residue₁_eq_modularRedLocHom (f * t) hg₁'
  obtain ⟨k₂, hk₂⟩ := R.residue₁_eq_modularRedLocHom (frickeInvolutionBar (1 * q) (f * t)) hg₂'
  have h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg₁'⟩ ∈ modularFunctionFieldC k 1 := by
    rw [← hk₁]; exact SetLike.coe_mem _
  have h₂F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg₂'⟩ ∈ modularFunctionFieldC k 1 := by
    rw [← hk₂]; exact SetLike.coe_mem _
  obtain ⟨c₀, hv₁, hv₂⟩ := exists_hasValue_frobNodePair_of_forall_pole_not_centred red a ha ha2 (f * t)
    hg₁' h₁F hg₂' h₂F (fun W hW hcen => absurd (hpole W hcen) (not_le.mpr hW))

  set r₁f : ↥(modularFunctionFieldC k 1) := R.residue₁ ⟨f, hf₁⟩ with hr₁f
  set r₁t : ↥(modularFunctionFieldC k 1) := R.residue₁ ⟨t, ht₁⟩ with hr₁t
  set r₂f : ↥(modularFunctionFieldC k 1) := R.residue₂ ⟨f, hf₂⟩ with hr₂f
  set r₂t : ↥(modularFunctionFieldC k 1) := R.residue₂ ⟨t, ht₂⟩ with hr₂t
  have hid₁ : (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1)) = r₁f * r₁t := by
    apply Subtype.ext
    show CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg₁'⟩ = ((r₁f * r₁t : ↥(modularFunctionFieldC k 1)) : LaurentSeries k)
    rw [← hk₁, hr₁f, hr₁t, ← map_mul, LevelOneProlongationPair.residue₁_apply]
    rfl
  have hid₂ : (⟨_, h₂F⟩ : ↥(modularFunctionFieldC k 1)) = r₂f * r₂t := by
    apply Subtype.ext
    show CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg₂'⟩ = ((r₂f * r₂t : ↥(modularFunctionFieldC k 1)) : LaurentSeries k)
    rw [← hk₂, hr₂f, hr₂t, ← map_mul, LevelOneProlongationPair.residue₂_apply, R.residue₂_eq]
    rfl
  rw [hid₁] at hv₁
  rw [hid₂] at hv₂

  set J₁ : ↥(modularFunctionFieldC k 1) :=
    (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) a with hJ₁
  set J₂ : ↥(modularFunctionFieldC k 1) :=
    (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) (a ^ q) with hJ₂
  have hoJ₁ : (frobNodePair q a).1.ord J₁ = 1 := ord_charLGeomPlaceOfPoint_jqModC_sub k a
  have hoJ₂ : (frobNodePair q a).2.ord J₂ = 1 := ord_charLGeomPlaceOfPoint_jqModC_sub k (a ^ q)
  have hJ₁0 : J₁ ≠ 0 := by intro h; rw [h, Place.ord_zero] at hoJ₁; exact zero_ne_one hoJ₁
  have hJ₂0 : J₂ ≠ 0 := by intro h; rw [h, Place.ord_zero] at hoJ₂; exact zero_ne_one hoJ₂

  have hsplit₁ : r₁f * r₁t = (J₁ ^ n₁ * r₁f) * (J₁ ^ (-n₁) * r₁t) := by
    rw [zpow_neg]
    field_simp
  have hsplit₂ : r₂f * r₂t = (J₂ ^ n₂ * r₂f) * (J₂ ^ (-n₂) * r₂t) := by
    rw [zpow_neg]
    field_simp
  rw [hsplit₁] at hv₁
  rw [hsplit₂] at hv₂
  have htv₁ := hasValue_of_mul htw₁ hl₁ hv₁
  have htv₂ := hasValue_of_mul htw₂ hl₂ hv₂
  refine ⟨fun hne => ?_, fun hne => ?_, ⟨c₀ * l₁⁻¹ * l₂⁻¹, ?_, ?_⟩⟩
  ·
    have hmem := htv₁.mem
    have h0 := Place.ord_nonneg_of_mem _ hmem
    rw [Place.ord_mul _ (zpow_ne_zero n₁ hJ₁0) hne, Place.ord_zpow, hoJ₁, mul_one] at h0
    change -n₁ ≤ (frobNodePair q a).1.ord r₁f
    omega
  · have hmem := htv₂.mem
    have h0 := Place.ord_nonneg_of_mem _ hmem
    rw [Place.ord_mul _ (zpow_ne_zero n₂ hJ₂0) hne, Place.ord_zpow, hoJ₂, mul_one] at h0
    change -n₂ ≤ (frobNodePair q a).2.ord r₂f
    omega
  · have : l₂ * (c₀ * l₁⁻¹ * l₂⁻¹) = c₀ * l₁⁻¹ := by field_simp
    rw [this]; exact htv₁
  · have : l₁ * (c₀ * l₁⁻¹ * l₂⁻¹) = c₀ * l₂⁻¹ := by field_simp
    rw [this]; exact htv₂

end FltWs24.N3

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
    (f t : ↥(modularFunctionFieldBar (1 * q)))
    (hf₁ : f ∈ R.R₁.integers) (hf₂ : f ∈ R.R₂.integers) (ht₁ : t ∈ R.R₁.integers) (ht₂ : t ∈ R.R₂.integers)
    (hpole : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → 0 ≤ W.ord (f * t))
    (n₁ n₂ : ℤ) (l₁ l₂ : k) (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (htw₁ : (frobNodePair q a).1.HasValue
      (((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) a) ^ (-n₁)
        * (R.residue₁ ⟨t, ht₁⟩ : ↥(modularFunctionFieldC k 1))) l₁)
    (htw₂ : (frobNodePair q a).2.HasValue
      (((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) (a ^ q)) ^ (-n₂)
        * (R.residue₂ ⟨t, ht₂⟩ : ↥(modularFunctionFieldC k 1))) l₂) :
    (R.residue₁ ⟨f, hf₁⟩ ≠ 0 → -n₁ ≤ (frobNodePair q a).1.ord (R.residue₁ ⟨f, hf₁⟩ : ↥(modularFunctionFieldC k 1))) ∧
    (R.residue₂ ⟨f, hf₂⟩ ≠ 0 → -n₂ ≤ (frobNodePair q a).2.ord (R.residue₂ ⟨f, hf₂⟩ : ↥(modularFunctionFieldC k 1))) ∧
    ∃ c : k,
      (frobNodePair q a).1.HasValue
        (((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) a) ^ n₁
          * (R.residue₁ ⟨f, hf₁⟩ : ↥(modularFunctionFieldC k 1))) (l₂ * c) ∧
      (frobNodePair q a).2.HasValue
        (((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) (a ^ q)) ^ n₂
          * (R.residue₂ ⟨f, hf₂⟩ : ↥(modularFunctionFieldC k 1))) (l₁ * c) :=
  FltWs24.N3.main R a ha ha2 f t hf₁ hf₂ ht₁ ht₂ hpole n₁ n₂ l₁ l₂ hl₁ hl₂ htw₁ htw₂

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_le_ord_residue_and_exists_hasValue_of_mul
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_le_ord_residue_and_exists_hasValue_of_mul (solution)
