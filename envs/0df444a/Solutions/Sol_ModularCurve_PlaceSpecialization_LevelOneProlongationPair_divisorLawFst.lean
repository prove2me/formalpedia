-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.divisorLawFst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/59476ee9-7bfd-529e-af04-772865ce5500

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_ord_pencil_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_residue_fst_eq_zero_of_forall_ne
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_sp_eq_placeInfty_of_forall_ord_le_zero
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental_of_isSeparable
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_divisorLawFst
p2m_attr_erase "instance" "instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~frobOnPlacesGeomLevel_charLGeomPlaceOfPoint"

noncomputable section

namespace Ws25
namespace PSFst

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~frobOnPlacesGeomLevel_charLGeomPlaceOfPoint ModularCurve.PlaceSpecialization Polynomial"

section PlaceHelpers

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_pos_iff_inv_not_mem (x : F) : 0 < v.ord x ↔ x⁻¹ ∉ v.toValuationSubring := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [Place.ord_zero, lt_self_iff_false, inv_zero, ZeroMemClass.zero_mem,
      not_true_eq_false]
  · rw [v.mem_iff_ord_nonneg (inv_ne_zero hx), v.ord_inv]
    omega

theorem mem_of_ord_pos {x : F} (h : 0 < v.ord x) : x ∈ v.toValuationSubring := by
  have hx : x ≠ 0 := by rintro rfl; simp at h
  exact (v.mem_iff_ord_nonneg hx).mpr h.le

theorem ord_algebraMap' {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have hc' : algebraMap K F c ≠ 0 := (_root_.map_ne_zero (algebraMap K F)).mpr hc
  have hu : IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) :=
    ⟨⟨⟨algebraMap K F c, v.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simpa using mul_inv_cancel₀ hc'),
      Subtype.ext (by simpa using inv_mul_cancel₀ hc')⟩, rfl⟩
  obtain ⟨u, hu⟩ := hu
  have := v.ord_coe_unit u
  rwa [hu] at this

theorem ord_add_pos {x y : F} (hx : 0 < v.ord x) (hy : 0 < v.ord y) (hxy : x + y ≠ 0) :
    0 < v.ord (x + y) := by

  rw [ord_pos_iff_inv_not_mem]
  intro hinv
  have hxm := mem_of_ord_pos v hx
  have hym := mem_of_ord_pos v hy
  have hsm : x + y ∈ v.toValuationSubring := add_mem hxm hym

  have hu : IsUnit (⟨x + y, hsm⟩ : v.toValuationSubring) :=
    ⟨⟨⟨x + y, hsm⟩, ⟨(x + y)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hxy),
      Subtype.ext (inv_mul_cancel₀ hxy)⟩, rfl⟩
  have hxn : ¬ IsUnit (⟨x, hxm⟩ : v.toValuationSubring) := fun h => by
    have := v.ord_coe_unit h.unit
    simp only [IsUnit.unit_spec] at this
    rw [this] at hx; exact lt_irrefl _ hx
  have hyn : ¬ IsUnit (⟨y, hym⟩ : v.toValuationSubring) := fun h => by
    have := v.ord_coe_unit h.unit
    simp only [IsUnit.unit_spec] at this
    rw [this] at hy; exact lt_irrefl _ hy
  have hxM : (⟨x, hxm⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.mem_maximalIdeal _).mpr hxn
  have hyM : (⟨y, hym⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.mem_maximalIdeal _).mpr hyn
  have : (⟨x + y, hsm⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ := add_mem hxM hyM
  exact (IsLocalRing.mem_maximalIdeal _).mp this hu

theorem ord_add_pos' {x y : F} (hx : 0 < v.ord x) (hy : y = 0 ∨ 0 < v.ord y) (hxy : x + y ≠ 0) :
    0 < v.ord (x + y) := by
  rcases hy with rfl | hy
  · rwa [add_zero]
  · exact ord_add_pos v hx hy hxy

theorem ord_algebraMap_mul {c : K} (hc : c ≠ 0) (x : F) :
    v.ord (algebraMap K F c * x) = v.ord x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [mul_zero]
  · rw [v.ord_mul ((_root_.map_ne_zero _).mpr hc) hx, ord_algebraMap' v hc, zero_add]

theorem ord_neg (x : F) : v.ord (-x) = v.ord x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [neg_zero]
  · have h : (-x) = algebraMap K F (-1) * x := by rw [map_neg, map_one, neg_one_mul]
    rw [h, ord_algebraMap_mul v (neg_ne_zero.mpr one_ne_zero)]

theorem algebraMap_eq_of_ord_sub_pos (f : F) {x x' : K} (h : 0 < v.ord (f - algebraMap K F x))
    (h' : 0 < v.ord (f - algebraMap K F x')) : x = x' := by
  by_contra hne
  have hc : x' - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hd : (f - algebraMap K F x) + -(f - algebraMap K F x') = algebraMap K F (x' - x) := by
    rw [map_sub]; ring
  have hpos := ord_add_pos v h (by rw [ord_neg]; exact h') (by rw [hd]; exact (_root_.map_ne_zero _).mpr hc)
  rw [hd, ord_algebraMap' v hc] at hpos
  exact lt_irrefl _ hpos

end PlaceHelpers

section JLine

variable (k : Type*) [Field k]

theorem ratFuncEquivCharLOneC_X : ratFuncEquivCharLOneC k RatFunc.X = (⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) := by
  apply Subtype.ext
  simp only [ratFuncEquivCharLOneC, AlgEquiv.trans_apply]
  exact RatFunc.algEquivOfTranscendental_X (f := jqModC k) (h := transcendental_jqModC k)

theorem ord_charLGeomPlaceEquiv (v₀ : Place k (RatFunc k)) (f : RatFunc k) :
    (charLGeomPlaceEquiv k v₀).ord (ratFuncEquivCharLOneC k f) = v₀.ord f :=
  Place.ord_congrRingEquiv (ratFuncEquivCharLOneC k).toRingEquiv
    (fun a => (ratFuncEquivCharLOneC k).commutes a) v₀ f

theorem ord_placeOfPoint_X_sub_C_pos (a : k) :
    0 < (RationalFunctionField.placeOfPoint k a).ord (RatFunc.X - algebraMap k (RatFunc k) a) := by
  have hq : (X - C a : k[X]) ≠ 0 := X_sub_C_ne_zero a
  have hmap : algebraMap k[X] (RatFunc k) (X - C a) = RatFunc.X - algebraMap k (RatFunc k) a := by
    rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  rw [RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum, ← hmap]
  have hne : (Place.ofHeightOneSpectrum (K := k) (F := RatFunc k)
      (RationalFunctionField.heightOneSpectrumOfIrreducible k (irreducible_X_sub_C a))).ord
        (algebraMap k[X] (RatFunc k) (X - C a)) ≠ 0 := by
    rw [Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := k) (F := RatFunc k) _ hq,
      RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal]
    exact Ideal.mem_span_singleton_self _
  have hnn : 0 ≤ (Place.ofHeightOneSpectrum (K := k) (F := RatFunc k)
      (RationalFunctionField.heightOneSpectrumOfIrreducible k (irreducible_X_sub_C a))).ord
        (algebraMap k[X] (RatFunc k) (X - C a)) :=
    Place.ord_nonneg_of_mem _ (RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum k _ _)
  omega

theorem ord_jt_sub_pos (a : k) : 0 < (charLGeomPlaceOfPoint k a).ord ((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) - algebraMap k (modularFunctionFieldC k 1) a) := by
  have key : ((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) - algebraMap k (modularFunctionFieldC k 1) a) = ratFuncEquivCharLOneC k (RatFunc.X - algebraMap k (RatFunc k) a) := by
    rw [map_sub, ratFuncEquivCharLOneC_X, AlgEquiv.commutes]
  show 0 < (charLGeomPlaceEquiv k (RationalFunctionField.placeOfPoint k a)).ord ((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) - algebraMap k (modularFunctionFieldC k 1) a)
  rw [key, ord_charLGeomPlaceEquiv]
  exact ord_placeOfPoint_X_sub_C_pos k a

theorem jt_mem_charLGeomPlaceOfPoint (a : k) : (⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) ∈ (charLGeomPlaceOfPoint k a).toValuationSubring := by
  have h1 : ((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) - algebraMap k (modularFunctionFieldC k 1) a) ∈ (charLGeomPlaceOfPoint k a).toValuationSubring := mem_of_ord_pos _ (ord_jt_sub_pos k a)
  have h2 : algebraMap k (modularFunctionFieldC k 1) a ∈ (charLGeomPlaceOfPoint k a).toValuationSubring := (charLGeomPlaceOfPoint k a).algebraMap_mem' a
  have : (⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) = ((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) - algebraMap k (modularFunctionFieldC k 1) a) + algebraMap k (modularFunctionFieldC k 1) a := by ring
  rw [this]; exact add_mem h1 h2

theorem ord_jt_nonneg (a : k) : 0 ≤ (charLGeomPlaceOfPoint k a).ord (⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) :=
  Place.ord_nonneg_of_mem _ (jt_mem_charLGeomPlaceOfPoint k a)

theorem ord_jt_placeInfty_neg [DecidableEq (RatFunc k)] :
    (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).ord (⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) < 0 := by
  rw [← ratFuncEquivCharLOneC_X, ord_charLGeomPlaceEquiv]
  by_contra hge
  push_neg at hge
  have hmem := Place.mem_of_ord_nonneg _ (RatFunc.X_ne_zero (K := k)) hge
  rw [RationalFunctionField.placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff,
    RatFunc.inftyValuation.X, ← WithZero.exp_zero, WithZero.exp_le_exp] at hmem
  exact absurd hmem (by norm_num)

theorem charLGeomPlaceOfPoint_ne_placeInfty [DecidableEq (RatFunc k)] (a : k) :
    charLGeomPlaceOfPoint k a ≠ charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := fun h =>
  absurd (ord_jt_placeInfty_neg k) (not_lt.mpr (h ▸ ord_jt_nonneg k a))

variable {q : ℕ} [Fact q.Prime] [CharP k q] (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)

theorem frobOnPlacesGeomLevel_charLGeomPlaceOfPoint (a : k) :
    frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceOfPoint k a) = charLGeomPlaceOfPoint k (a ^ q) := by
  haveI : CharP (modularFunctionFieldC k 1) q :=
    charP_of_injective_algebraMap (algebraMap k (modularFunctionFieldC k 1)).injective q
  apply ModularCurve.eq_charLGeomPlaceOfPoint_of_ord_pos
  rw [ord_pos_iff_inv_not_mem, mem_frobOnPlacesGeomLevel_iff, map_inv₀, map_sub,
    frobeniusGeomLevel_jq, AlgHom.commutes, map_pow, ← sub_pow_char, ← inv_pow]
  intro hmem
  have h := (ord_pos_iff_inv_not_mem (charLGeomPlaceOfPoint k a) ((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) - algebraMap k (modularFunctionFieldC k 1) a)).mp (ord_jt_sub_pos k a)
  exact h (((charLGeomPlaceOfPoint k a).toValuationSubring.pow_mem_iff (Fact.out : q.Prime).ne_zero _).mp hmem)

end JLine

section LevelQ

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

local notation "QQ" => AlgebraicClosure ℚ
local notation "FF" => modularFunctionFieldBar (1 * q)

def jOne : modularFunctionFieldBar 1 :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full 1 (jq_mem 1))⟩

theorem jFun_eq_heckeAlphaBar_jOne :
    (jFun (q := q) : FF) = heckeAlphaBar QQ 1 q jOne :=
  Subtype.ext (coe_heckeAlphaBar 1 q jOne).symm

theorem jqFun_eq_heckeBetaBar_jOne :
    (jqFun (q := q) : FF) = heckeBetaBar QQ 1 q jOne := by
  apply Subtype.ext
  show coeffEmb QQ (qExpand ℚ (1 * q) jq) = qExpand QQ q (coeffEmb QQ jq)
  show coeffMap (algebraMap ℚ QQ) (qExpand ℚ (1 * q) (jqModC ℚ))
    = qExpand QQ q (coeffMap (algebraMap ℚ QQ) (jqModC ℚ))
  rw [coeffMap_qExpand, coeffMap_jqModC]
  exact qExpand_congr (one_mul q) _

variable (P : PlaceSpecialization A q 1 data hKr k red hα hβ)

theorem redSnd_eq_placeInfty_of_forall_ord_le_zero [DecidableEq (RatFunc k)]
    (W : Place QQ FF)
    (hW : ∀ b : A, W.ord ((jqFun (q := q) : FF) - algebraMap QQ FF (b : QQ)) ≤ 0) :
    P.redSnd W = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := by
  suffices key : (letI := Classical.decEq (RatFunc k);
      P.redSnd W = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)) by
    convert key
  show P.sp (W.restrictAlong (heckeBetaBar QQ 1 q) hβ) = _
  refine P.sp_eq_placeInfty_of_forall_ord_le_zero _ fun b => ?_
  have h := hW b
  rw [jqFun_eq_heckeBetaBar_jOne, ← (heckeBetaBar QQ 1 q).commutes (b : QQ), ← map_sub,
    Place.ord_restrictAlong _ hβ] at h
  have hepos : 0 < (Place.ramificationIndexAlong (heckeBetaBar QQ 1 q) W : ℤ) := by
    letI := algebraAlong (heckeBetaBar QQ 1 q)
    haveI := isScalarTower_along (heckeBetaBar QQ 1 q)
    haveI := isIntegral_along (heckeBetaBar QQ 1 q) hβ
    exact_mod_cast Place.ramificationIndex_pos (F := modularFunctionFieldBar 1) W
  by_contra hpos
  push_neg at hpos
  exact absurd h (not_le.mpr (mul_pos hepos hpos))

theorem redFst_eq_placeInfty_of_forall_ord_le_zero' [DecidableEq (RatFunc k)]
    (W : Place QQ FF)
    (hW : ∀ a : A, W.ord ((jFun (q := q) : FF) - algebraMap QQ FF (a : QQ)) ≤ 0) :
    P.redFst W = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := by
  suffices key : (letI := Classical.decEq (RatFunc k);
      P.redFst W = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)) by
    convert key
  show P.sp (W.restrictAlong (heckeAlphaBar QQ 1 q) hα) = _
  refine P.sp_eq_placeInfty_of_forall_ord_le_zero _ fun b => ?_
  have h := hW b
  rw [jFun_eq_heckeAlphaBar_jOne, ← (heckeAlphaBar QQ 1 q).commutes (b : QQ), ← map_sub,
    Place.ord_restrictAlong _ hα] at h
  have hepos : 0 < (Place.ramificationIndexAlong (heckeAlphaBar QQ 1 q) W : ℤ) := by
    letI := algebraAlong (heckeAlphaBar QQ 1 q)
    haveI := isScalarTower_along (heckeAlphaBar QQ 1 q)
    haveI := isIntegral_along (heckeAlphaBar QQ 1 q) hα
    exact_mod_cast Place.ramificationIndex_pos (F := modularFunctionFieldBar 1) W
  by_contra hpos
  push_neg at hpos
  exact absurd h (not_le.mpr (mul_pos hepos hpos))

end LevelQ

section OneClass

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}

local notation "QQ" => AlgebraicClosure ℚ
local notation "FF" => modularFunctionFieldBar (1 * q)
local notation "cst" => algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))

theorem liesOverPrime_of_ringHom {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) : A.LiesOverPrime q := by
  show ((q : ℕ) : QQ) ∈ A.nonunits
  have hq : red (q : A) = 0 := by rw [map_natCast, CharP.cast_eq_zero k q]
  have hmax : (q : A) ∈ IsLocalRing.maximalIdeal A :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top red) ((RingHom.mem_ker).mpr hq)
  refine ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨(q : A).2, ?_⟩
  simp at hmax
  exact hmax

theorem isUnit_of_map_ne_zero {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) {u : A} (hu : red u ≠ 0) : IsUnit u := by
  by_contra hnu
  apply hu
  have hmax : u ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
  exact ValuationSubring.map_eq_zero_of_valuation_lt_one_of_charP A q (liesOverPrime_of_ringHom red)
    red u ((A.valuation_lt_one_iff u).mp hmax)

theorem jqFun_sub_algebraMap_ne_zero (c : QQ) : (jqFun (q := q) : FF) - cst c ≠ 0 := by
  intro h
  have h1 : ((jqFun (q := q) : FF) : LaurentSeries QQ) = ((cst c : FF) : LaurentSeries QQ) := by
    rw [sub_eq_zero.mp h]
  have h2 := congrArg (fun s : LaurentSeries QQ => s.coeff ((1 * q : ℕ) * (-1 : ℤ))) h1
  have hl : ((jqFun (q := q) : FF) : LaurentSeries QQ).coeff ((1 * q : ℕ) * (-1 : ℤ)) = 1 := by
    show (coeffEmb QQ (qExpand ℚ (1 * q) jq)).coeff _ = 1
    show (coeffMap (algebraMap ℚ QQ) (qExpand ℚ (1 * q) (jqModC ℚ))).coeff _ = 1
    rw [coeffMap_qExpand, coeffMap_jqModC, qExpand_coeff_mul, coeff_jqModC_neg_one]
  have hr : ((cst c : FF) : LaurentSeries QQ).coeff ((1 * q : ℕ) * (-1 : ℤ)) = 0 := by
    show (algebraMap QQ (LaurentSeries QQ) c).coeff _ = 0
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne]
    have : (0 : ℤ) < (1 * q : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (1 * q))
    omega
  rw [hl, hr] at h2
  exact one_ne_zero h2

theorem jFun_sub_algebraMap_ne_zero (c : QQ) : (jFun (q := q) : FF) - cst c ≠ 0 := by
  intro h
  have h1 : ((jFun (q := q) : FF) : LaurentSeries QQ) = ((cst c : FF) : LaurentSeries QQ) := by
    rw [sub_eq_zero.mp h]
  have h2 := congrArg (fun s : LaurentSeries QQ => s.coeff (-1 : ℤ)) h1
  have hl : ((jFun (q := q) : FF) : LaurentSeries QQ).coeff (-1 : ℤ) = 1 := by
    show (coeffEmb QQ jq).coeff _ = 1
    show (coeffMap (algebraMap ℚ QQ) (jqModC ℚ)).coeff _ = 1
    rw [coeffMap_jqModC, coeff_jqModC_neg_one]
  have hr : ((cst c : FF) : LaurentSeries QQ).coeff (-1 : ℤ) = 0 := by
    show (algebraMap QQ (LaurentSeries QQ) c).coeff _ = 0
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne]
    omega
  rw [hl, hr] at h2
  exact one_ne_zero h2

theorem red_eq_red_of_not_finite (W : Place QQ FF)
    (hW : ¬ ((∃ a : A, 0 < W.ord ((jFun (q := q) : FF) - cst (a : QQ))) ∧
            (∃ b : A, 0 < W.ord ((jqFun (q := q) : FF) - cst (b : QQ)))))
    (l l' z z' : A)
    (h : 0 < W.ord ((jFun (q := q) : FF) + cst (l : QQ) * jqFun (q := q) - cst (z : QQ)))
    (h' : 0 < W.ord ((jFun (q := q) : FF) + cst (l' : QQ) * jqFun (q := q) - cst (z' : QQ))) :
    red l = red l' := by
  by_cases hjq : ∃ b : A, 0 < W.ord ((jqFun (q := q) : FF) - cst (b : QQ))
  ·
    exfalso
    obtain ⟨b, hb⟩ := hjq
    apply hW
    refine ⟨⟨z - l * b, ?_⟩, ⟨b, hb⟩⟩
    have e : (jFun (q := q) : FF) - cst ((z - l * b : A) : QQ)
        = ((jFun (q := q) : FF) + cst (l : QQ) * jqFun (q := q) - cst (z : QQ))
          + -(cst (l : QQ) * ((jqFun (q := q) : FF) - cst (b : QQ))) := by
      push_cast
      ring
    rw [e]
    refine ord_add_pos' W h ?_ (by rw [← e]; exact jFun_sub_algebraMap_ne_zero _)
    rcases eq_or_ne (l : QQ) 0 with hl0 | hl0
    · left; rw [hl0, map_zero, zero_mul, neg_zero]
    · right; rw [ord_neg, ord_algebraMap_mul W hl0]; exact hb
  · push_neg at hjq

    by_contra hne
    have hu : IsUnit (l - l') := isUnit_of_map_ne_zero (q := q) red (by rwa [map_sub, sub_ne_zero])
    have hu0 : ((l - l' : A) : QQ) ≠ 0 := fun h0 => hu.ne_zero (Subtype.ext (by simpa using h0))
    set d : FF := cst ((l - l' : A) : QQ) * jqFun (q := q) - cst ((z - z' : A) : QQ) with hd
    have hd' : d = ((jFun (q := q) : FF) + cst (l : QQ) * jqFun (q := q) - cst (z : QQ))
        + -((jFun (q := q) : FF) + cst (l' : QQ) * jqFun (q := q) - cst (z' : QQ)) := by
      rw [hd]; push_cast; ring

    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h1 : ((l - l' : A) : QQ) * (w : QQ) = 1 := by exact_mod_cast congrArg Subtype.val hw
    have hdiv : d = cst ((l - l' : A) : QQ) * ((jqFun (q := q) : FF) - cst (((z - z') * w : A) : QQ)) := by
      rw [hd, mul_sub, ← map_mul]
      congr 2
      push_cast at h1 ⊢
      linear_combination (-((z : QQ) - (z' : QQ))) * h1
    have hd0 : d ≠ 0 := by
      rw [hdiv]
      exact mul_ne_zero ((_root_.map_ne_zero _).mpr hu0) (jqFun_sub_algebraMap_ne_zero _)
    have hdpos : 0 < W.ord d := by
      rw [hd']
      exact ord_add_pos W h (by rw [ord_neg]; exact h') (by rw [← hd']; exact hd0)
    rw [hdiv, ord_algebraMap_mul W hu0] at hdpos
    exact absurd hdpos (not_lt.mpr (hjq _))

end OneClass

section PrincipalDivisors

variable (k : Type*) [Field k]

theorem transcendental_jt : Transcendental k (⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) := fun h =>
  ModularCurve.transcendental_jqModC k (h.algHom (modularFunctionFieldC k 1).val)

theorem adjoin_jt_eq_top : IntermediateField.adjoin k ({(⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1)} : Set (modularFunctionFieldC k 1)) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨y, hy⟩ -
  have hy' : y ∈ IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k)) := by
    rw [← modularFunctionFieldC_one]; exact hy

  suffices H : ∀ w, w ∈ IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k)) →
      ∃ hw : w ∈ (modularFunctionFieldC k 1), (⟨w, hw⟩ : (modularFunctionFieldC k 1)) ∈ IntermediateField.adjoin k ({(⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1)} : Set (modularFunctionFieldC k 1)) by
    obtain ⟨hw, h⟩ := H y hy'
    exact h
  intro w hw
  induction hw using IntermediateField.adjoin_induction with
  | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨jqModC_mem k 1, IntermediateField.subset_adjoin k _ (Set.mem_singleton _)⟩
  | algebraMap c =>
      refine ⟨(modularFunctionFieldC k 1).algebraMap_mem c, ?_⟩
      have : (⟨algebraMap k (LaurentSeries k) c, (modularFunctionFieldC k 1).algebraMap_mem c⟩ : (modularFunctionFieldC k 1))
          = algebraMap k (modularFunctionFieldC k 1) c := rfl
      rw [this]; exact IntermediateField.algebraMap_mem _ c
  | add x y _ _ hx hy =>
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      refine ⟨add_mem hx1 hy1, ?_⟩
      have : (⟨x + y, add_mem hx1 hy1⟩ : (modularFunctionFieldC k 1)) = ⟨x, hx1⟩ + ⟨y, hy1⟩ := rfl
      rw [this]; exact add_mem hx2 hy2
  | inv x _ hx =>
      obtain ⟨hx1, hx2⟩ := hx
      refine ⟨IntermediateField.inv_mem _ hx1, ?_⟩
      have : (⟨x⁻¹, IntermediateField.inv_mem _ hx1⟩ : (modularFunctionFieldC k 1)) = (⟨x, hx1⟩ : (modularFunctionFieldC k 1))⁻¹ := rfl
      rw [this]; exact IntermediateField.inv_mem _ hx2
  | mul x y _ _ hx hy =>
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      refine ⟨mul_mem hx1 hy1, ?_⟩
      have : (⟨x * y, mul_mem hx1 hy1⟩ : (modularFunctionFieldC k 1)) = ⟨x, hx1⟩ * ⟨y, hy1⟩ := rfl
      rw [this]; exact mul_mem hx2 hy2

theorem hasPrincipalDivisors_charLOne : AlgebraicCurve.HasPrincipalDivisors k (modularFunctionFieldC k 1) := by
  have htop := adjoin_jt_eq_top k
  refine AlgebraicCurve.hasPrincipalDivisors_of_transcendental_of_isSeparable (transcendental_jt k) ?_ ?_
  · rw [htop]
    refine ⟨⟨{1}, ?_⟩⟩
    rw [Finset.coe_singleton, eq_top_iff]
    rintro y -
    refine Submodule.mem_span_singleton.mpr ⟨⟨y, IntermediateField.mem_top⟩, ?_⟩
    rw [IntermediateField.smul_def, smul_eq_mul, mul_one]
  · rw [htop]
    refine ⟨fun y => ?_⟩
    have : y = algebraMap (⊤ : IntermediateField k (modularFunctionFieldC k 1)) (modularFunctionFieldC k 1) ⟨y, IntermediateField.mem_top⟩ := rfl
    rw [this]
    exact isSeparable_algebraMap _

end PrincipalDivisors

end Ws25.PSFst

namespace Ws25
namespace Isolation

open Finset

theorem eq_of_pow_char_eq {k : Type*} [Field k] (q : ℕ) [Fact q.Prime] [CharP k q] {s t : k}
    (h : s ^ q = t ^ q) : s = t := by
  have : (s - t) ^ q = 0 := by rw [sub_pow_char, h, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (Fact.out : q.Prime).ne_zero |>.mp this)

theorem apply_eq_zero_of_forall_sum_fiber_eq_zero {k : Type*} [Field k] [DecidableEq k]
    (q : ℕ) [Fact q.Prime] [CharP k q] (X Y : k →₀ ℤ) (S : Set k) (hS : S.Infinite)
    (h : ∀ l ∈ S, ∀ c : k,
      (∑ a ∈ X.support.filter (fun a => a + l * a ^ q = c), X a) +
        (∑ b ∈ Y.support.filter (fun b => b ^ q + l * b = c), Y b) = 0)
    (a₀ : k) (ha₀ : a₀ ^ (q * q) ≠ a₀) : X a₀ = 0 := by
  by_contra hX
  have ha₀s : a₀ ∈ X.support := Finsupp.mem_support_iff.mpr hX

  let badX : Finset k := (X.support.erase a₀).image fun s => (a₀ - s) / (s ^ q - a₀ ^ q)
  let badY : Finset k := (Y.support.erase (a₀ ^ q)).image fun t => (a₀ - t ^ q) / (t - a₀ ^ q)
  obtain ⟨l, hlS, hlbad⟩ := hS.exists_notMem_finset (badX ∪ badY)
  have hlX : l ∉ badX := fun hm => hlbad (mem_union_left _ hm)
  have hlY : l ∉ badY := fun hm => hlbad (mem_union_right _ hm)
  set c := a₀ + l * a₀ ^ q with hc

  have hfibX : X.support.filter (fun a => a + l * a ^ q = c) = {a₀} := by
    ext s
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hs, hsc⟩
      by_contra hne
      apply hlX
      refine mem_image.mpr ⟨s, mem_erase.mpr ⟨hne, hs⟩, ?_⟩
      have hsq : s ^ q - a₀ ^ q ≠ 0 := fun h0 =>
        hne (eq_of_pow_char_eq q (sub_eq_zero.mp h0))
      rw [div_eq_iff hsq]
      rw [hc] at hsc
      linear_combination -hsc
    · rintro rfl
      exact ⟨ha₀s, rfl⟩

  have hfibY : Y.support.filter (fun b => b ^ q + l * b = c) = ∅ := by
    ext t
    simp only [mem_filter, Finset.notMem_empty, iff_false, not_and]
    intro ht htc
    rw [hc] at htc
    by_cases hta : t = a₀ ^ q
    · apply ha₀
      rw [hta, ← pow_mul] at htc
      linear_combination htc
    · apply hlY
      refine mem_image.mpr ⟨t, mem_erase.mpr ⟨hta, ht⟩, ?_⟩
      rw [div_eq_iff (sub_ne_zero.mpr hta)]
      linear_combination -htc
  have := h l hlS c
  rw [hfibX, hfibY, sum_singleton, sum_empty, add_zero] at this
  exact hX this

theorem sum_filter_eq_of_forall_pencil {k : Type*} [Field k] [DecidableEq k] (q : ℕ) [Fact q.Prime]
    [CharP k q] {ι : Type*} [DecidableEq ι] (supp : Finset ι) (D : ι → ℤ)
    (fin : ι → Prop) [DecidablePred fin] (a b : ι → k)
    (hdich : ∀ W ∈ supp, fin W → b W = a W ^ q ∨ a W = b W ^ q)
    (r₁ r₂ : k →₀ ℤ) (S : Set k) (hS : S.Infinite)
    (hT : ∀ l ∈ S, ∀ c : k,
      (∑ W ∈ supp.filter (fun W => fin W ∧ a W + l * b W = c), D W)
        = (∑ x ∈ r₁.support.filter (fun x => x + l * x ^ q = c), r₁ x)
          + (∑ y ∈ r₂.support.filter (fun y => y ^ q + l * y = c), r₂ y))
    (a₀ : k) (ha₀ : a₀ ^ (q * q) ≠ a₀) :
    (∑ W ∈ supp.filter (fun W => fin W ∧ a W = a₀ ∧ b W = a₀ ^ q), D W) = r₁ a₀ := by

  let S₁ : k → ℤ := fun x => ∑ W ∈ supp.filter (fun W => fin W ∧ a W = x ∧ b W = x ^ q), D W
  let S₂ : k → ℤ := fun y =>
    ∑ W ∈ supp.filter (fun W => fin W ∧ a W = y ^ q ∧ b W = y ∧ y ^ (q * q) ≠ y), D W
  let U₁ : Finset k := supp.image a ∪ r₁.support
  let U₂ : Finset k := supp.image b ∪ r₂.support
  have hS₁ : ∀ x, x ∉ U₁ → S₁ x = 0 := by
    intro x hx
    apply Finset.sum_eq_zero
    intro W hW
    exfalso; apply hx
    simp only [mem_filter] at hW
    exact mem_union_left _ (mem_image.mpr ⟨W, hW.1, hW.2.2.1⟩)
  have hS₂ : ∀ y, y ∉ U₂ → S₂ y = 0 := by
    intro y hy
    apply Finset.sum_eq_zero
    intro W hW
    exfalso; apply hy
    simp only [mem_filter] at hW
    exact mem_union_left _ (mem_image.mpr ⟨W, hW.1, hW.2.2.2.1⟩)
  let X : k →₀ ℤ := Finsupp.onFinset U₁ (fun x => S₁ x - r₁ x) (fun x hx => by
    by_contra hxU
    apply hx
    show S₁ x - r₁ x = 0
    rw [hS₁ x hxU, Finsupp.notMem_support_iff.mp (fun h => hxU (mem_union_right _ h)), sub_zero])
  let Y : k →₀ ℤ := Finsupp.onFinset U₂ (fun y => S₂ y - r₂ y) (fun y hy => by
    by_contra hyU
    apply hy
    show S₂ y - r₂ y = 0
    rw [hS₂ y hyU, Finsupp.notMem_support_iff.mp (fun h => hyU (mem_union_right _ h)), sub_zero])
  have hXa : ∀ x, X x = S₁ x - r₁ x := fun x => Finsupp.onFinset_apply
  have hYa : ∀ y, Y y = S₂ y - r₂ y := fun y => Finsupp.onFinset_apply

  have hN4 : ∀ l ∈ S, ∀ c : k,
      (∑ x ∈ X.support.filter (fun x => x + l * x ^ q = c), X x) +
        (∑ y ∈ Y.support.filter (fun y => y ^ q + l * y = c), Y y) = 0 := by
    intro l hl c

    have e1 : (∑ x ∈ X.support.filter (fun x => x + l * x ^ q = c), X x)
        = ∑ x ∈ U₁.filter (fun x => x + l * x ^ q = c), X x := by
      refine Finset.sum_subset (filter_subset_filter _ Finsupp.support_onFinset_subset) ?_
      intro x _ hx
      by_contra h
      exact hx (mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr h, (mem_filter.mp ‹x ∈ _›).2⟩)
    have e2 : (∑ y ∈ Y.support.filter (fun y => y ^ q + l * y = c), Y y)
        = ∑ y ∈ U₂.filter (fun y => y ^ q + l * y = c), Y y := by
      refine Finset.sum_subset (filter_subset_filter _ Finsupp.support_onFinset_subset) ?_
      intro y _ hy
      by_contra h
      exact hy (mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr h, (mem_filter.mp ‹y ∈ _›).2⟩)
    rw [e1, e2]
    simp only [hXa, hYa, Finset.sum_sub_distrib]

    have er1 : (∑ x ∈ U₁.filter (fun x => x + l * x ^ q = c), r₁ x)
        = ∑ x ∈ r₁.support.filter (fun x => x + l * x ^ q = c), r₁ x := by
      symm
      refine Finset.sum_subset (filter_subset_filter _ subset_union_right) ?_
      intro x _ hx
      by_contra h
      exact hx (mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr h, (mem_filter.mp ‹x ∈ _›).2⟩)
    have er2 : (∑ y ∈ U₂.filter (fun y => y ^ q + l * y = c), r₂ y)
        = ∑ y ∈ r₂.support.filter (fun y => y ^ q + l * y = c), r₂ y := by
      symm
      refine Finset.sum_subset (filter_subset_filter _ subset_union_right) ?_
      intro y _ hy
      by_contra h
      exact hy (mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr h, (mem_filter.mp ‹y ∈ _›).2⟩)

    let s₁ := supp.filter (fun W => fin W ∧ b W = a W ^ q ∧ a W + l * b W = c)
    let s₂ := supp.filter (fun W => fin W ∧ a W = b W ^ q ∧ b W ^ (q * q) ≠ b W ∧ a W + l * b W = c)
    have es1 : (∑ x ∈ U₁.filter (fun x => x + l * x ^ q = c), S₁ x) = ∑ W ∈ s₁, D W := by
      have hmaps : ∀ W ∈ s₁, a W ∈ U₁.filter (fun x => x + l * x ^ q = c) := by
        intro W hW
        simp only [s₁, mem_filter] at hW
        refine mem_filter.mpr ⟨mem_union_left _ (mem_image.mpr ⟨W, hW.1, rfl⟩), ?_⟩
        rw [← hW.2.2.1]; exact hW.2.2.2
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      refine Finset.sum_congr rfl fun x hx => ?_
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext W
      simp only [s₁, mem_filter]
      have hxc := (mem_filter.mp hx).2
      constructor
      · rintro ⟨hW, hf, hax, hbx⟩
        refine ⟨⟨hW, hf, by rw [hbx, hax], ?_⟩, hax⟩
        rw [hax, hbx]; exact hxc
      · rintro ⟨⟨hW, hf, hba, _⟩, hax⟩
        exact ⟨hW, hf, hax, by rw [hba, hax]⟩
    have es2 : (∑ y ∈ U₂.filter (fun y => y ^ q + l * y = c), S₂ y) = ∑ W ∈ s₂, D W := by
      have hmaps : ∀ W ∈ s₂, b W ∈ U₂.filter (fun y => y ^ q + l * y = c) := by
        intro W hW
        simp only [s₂, mem_filter] at hW
        refine mem_filter.mpr ⟨mem_union_left _ (mem_image.mpr ⟨W, hW.1, rfl⟩), ?_⟩
        rw [← hW.2.2.1]; exact hW.2.2.2.2
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      refine Finset.sum_congr rfl fun y hy => ?_
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext W
      simp only [s₂, mem_filter]
      have hyc := (mem_filter.mp hy).2
      constructor
      · rintro ⟨hW, hf, hay, hby, hyy⟩
        refine ⟨⟨hW, hf, by rw [hay, hby], by rw [hby]; exact hyy, ?_⟩, hby⟩
        rw [hay, hby]; exact hyc
      · rintro ⟨⟨hW, hf, hab, hbb, _⟩, hby⟩
        exact ⟨hW, hf, by rw [hab, hby], hby, by rw [← hby]; exact hbb⟩
    have eunion : (∑ W ∈ s₁, D W) + (∑ W ∈ s₂, D W)
        = ∑ W ∈ supp.filter (fun W => fin W ∧ a W + l * b W = c), D W := by
      rw [← Finset.sum_union]
      · refine Finset.sum_congr ?_ fun _ _ => rfl
        ext W
        simp only [s₁, s₂, mem_union, mem_filter]
        constructor
        · rintro (⟨hW, hf, _, hc⟩ | ⟨hW, hf, _, _, hc⟩) <;> exact ⟨hW, hf, hc⟩
        · rintro ⟨hW, hf, hc⟩
          rcases hdich W hW hf with h1 | h2
          · exact Or.inl ⟨hW, hf, h1, hc⟩
          · by_cases h1 : b W = a W ^ q
            · exact Or.inl ⟨hW, hf, h1, hc⟩
            · refine Or.inr ⟨hW, hf, h2, fun hfix => h1 ?_, hc⟩
              rw [h2, ← pow_mul, hfix]
      · rw [Finset.disjoint_left]
        intro W h1 h2
        simp only [s₁, s₂, mem_filter] at h1 h2
        apply h2.2.2.2.1
        rw [pow_mul, ← h2.2.2.1, ← h1.2.2.1]
    rw [er1, er2, es1, es2]
    have := hT l hl c
    rw [← eunion] at this
    linear_combination this
  have hX0 := apply_eq_zero_of_forall_sum_fiber_eq_zero q X Y S hS hN4 a₀ ha₀
  rw [hXa, sub_eq_zero] at hX0
  exact hX0

end Ws25.Isolation

namespace Ws25
namespace PSFst

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~frobOnPlacesGeomLevel_charLGeomPlaceOfPoint ModularCurve.PlaceSpecialization Polynomial"

section Main

open ModularCurve.PlaceSpecialization Finset

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

local notation "Qb" => AlgebraicClosure ℚ
local notation "FF" => modularFunctionFieldBar (1 * q)
local notation "Fb" => modularFunctionFieldC k 1
local notation "Pt" => charLGeomPlaceOfPoint k
local notation "φ" => frobOnPlacesGeomLevel k 1 data hKr

abbrev JVal (W : Place Qb FF) (x : A) : Prop :=
  0 < W.ord (jFun (q := q) - algebraMap Qb FF (x : Qb))

abbrev JqVal (W : Place Qb FF) (y : A) : Prop :=
  0 < W.ord (jqFun (q := q) - algebraMap Qb FF (y : Qb))

abbrev IsFin (W : Place Qb FF) : Prop := (∃ x : A, JVal (q := q) W x) ∧ (∃ y : A, JqVal (q := q) W y)

variable (P : PlaceSpecialization A q 1 data hKr k red hα hβ)

theorem redFst_eq_of_jVal {W : Place Qb FF} {x : A} (hx : JVal (q := q) W x) :
    P.redFst W = Pt (red x) := by
  refine redFst_eq_charLGeomPlaceOfPoint_of_ord_pos P W x ?_
  have h : 0 < W.ord ((jFun (q := q) : FF) - algebraMap Qb FF (x : Qb)) := hx
  rw [jFun_eq_heckeAlphaBar_jOne] at h
  exact h

theorem redSnd_eq_of_jqVal {W : Place Qb FF} {y : A} (hy : JqVal (q := q) W y) :
    P.redSnd W = Pt (red y) := by
  refine redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos P W y ?_
  have h : 0 < W.ord ((jqFun (q := q) : FF) - algebraMap Qb FF (y : Qb)) := hy
  rw [jqFun_eq_heckeBetaBar_jOne] at h
  exact h

include P in
theorem red_eq_of_jVal {W : Place Qb FF} {x x' : A} (hx : JVal (q := q) W x) (hx' : JVal (q := q) W x') :
    red x = red x' :=
  charLGeomPlaceOfPoint_injective k ((redFst_eq_of_jVal P hx).symm.trans (redFst_eq_of_jVal P hx'))

include P in
theorem red_eq_of_jqVal {W : Place Qb FF} {y y' : A} (hy : JqVal (q := q) W y) (hy' : JqVal (q := q) W y') :
    red y = red y' :=
  charLGeomPlaceOfPoint_injective k ((redSnd_eq_of_jqVal P hy).symm.trans (redSnd_eq_of_jqVal P hy'))

open Classical in

noncomputable def aOf (W : Place Qb FF) : k :=
  if h : ∃ x : A, JVal (q := q) W x then red h.choose else 0

open Classical in

noncomputable def bOf (W : Place Qb FF) : k :=
  if h : ∃ y : A, JqVal (q := q) W y then red h.choose else 0

include P in
theorem aOf_eq {W : Place Qb FF} {x : A} (hx : JVal (q := q) W x) : aOf (q := q) (red := red) W = red x := by
  classical
  have h : ∃ x : A, JVal (q := q) W x := ⟨x, hx⟩
  rw [aOf, dif_pos h]
  exact red_eq_of_jVal P h.choose_spec hx

include P in
theorem bOf_eq {W : Place Qb FF} {y : A} (hy : JqVal (q := q) W y) : bOf (q := q) (red := red) W = red y := by
  classical
  have h : ∃ y : A, JqVal (q := q) W y := ⟨y, hy⟩
  rw [bOf, dif_pos h]
  exact red_eq_of_jqVal P h.choose_spec hy

theorem redFst_eq_aOf {W : Place Qb FF} (hW : IsFin (q := q) (A := A) W) :
    P.redFst W = Pt (aOf (q := q) (red := red) W) := by
  obtain ⟨x, hx⟩ := hW.1
  rw [aOf_eq P hx]; exact redFst_eq_of_jVal P hx

theorem redSnd_eq_bOf {W : Place Qb FF} (hW : IsFin (q := q) (A := A) W) :
    P.redSnd W = Pt (bOf (q := q) (red := red) W) := by
  obtain ⟨y, hy⟩ := hW.2
  rw [bOf_eq P hy]; exact redSnd_eq_of_jqVal P hy

include P in

theorem bOf_eq_pow_or {W : Place Qb FF} (hW : IsFin (q := q) (A := A) W) :
    bOf (q := q) (red := red) W = aOf (q := q) (red := red) W ^ q ∨
      aOf (q := q) (red := red) W = bOf (q := q) (red := red) W ^ q := by
  have h1 := redFst_eq_aOf P hW
  have h2 := redSnd_eq_bOf P hW
  rcases P.d1 W with h | h
  ·
    right
    change P.redFst W = frobOnPlacesGeomLevel k 1 data hKr (P.redSnd W) at h
    rw [h1, h2, frobOnPlacesGeomLevel_charLGeomPlaceOfPoint k data hKr] at h
    exact charLGeomPlaceOfPoint_injective k h
  · left
    change frobOnPlacesGeomLevel k 1 data hKr (P.redFst W) = P.redSnd W at h
    rw [h1, h2, frobOnPlacesGeomLevel_charLGeomPlaceOfPoint k data hKr] at h
    exact (charLGeomPlaceOfPoint_injective k h).symm

include P in

theorem isStrictTypeOne_and_redFst_eq_iff {W : Place Qb FF} {a₀ : k} (ha₀ : a₀ ^ (q * q) ≠ a₀) :
    (P.IsStrictTypeOne W ∧ P.redFst W = Pt a₀) ↔
      (IsFin (q := q) (A := A) W ∧ aOf (q := q) (red := red) W = a₀ ∧ bOf (q := q) (red := red) W = a₀ ^ q) := by
  classical
  constructor
  · rintro ⟨hT, hF⟩
    have hφ : P.redSnd W = Pt (a₀ ^ q) := by
      rw [← frobOnPlacesGeomLevel_charLGeomPlaceOfPoint k data hKr, ← hF]
      exact hT.1.symm
    have hj : ∃ x : A, JVal (q := q) W x := by
      by_contra hno
      have := redFst_eq_placeInfty_of_forall_ord_le_zero' P W (fun x => not_lt.mp (fun h => hno ⟨x, h⟩))
      rw [hF] at this
      exact charLGeomPlaceOfPoint_ne_placeInfty k a₀ this
    have hjq : ∃ y : A, JqVal (q := q) W y := by
      by_contra hno
      have := redSnd_eq_placeInfty_of_forall_ord_le_zero P W (fun y => not_lt.mp (fun h => hno ⟨y, h⟩))
      rw [hφ] at this
      exact charLGeomPlaceOfPoint_ne_placeInfty k (a₀ ^ q) this
    have hW : IsFin (q := q) (A := A) W := ⟨hj, hjq⟩
    refine ⟨hW, charLGeomPlaceOfPoint_injective k ?_, charLGeomPlaceOfPoint_injective k ?_⟩
    · rw [← redFst_eq_aOf P hW, hF]
    · rw [← redSnd_eq_bOf P hW, hφ]
  · rintro ⟨hW, ha, hb⟩
    have h1 : P.redFst W = Pt a₀ := by rw [redFst_eq_aOf P hW, ha]
    have h2 : P.redSnd W = Pt (a₀ ^ q) := by rw [redSnd_eq_bOf P hW, hb]
    refine ⟨⟨?_, ?_⟩, h1⟩
    · change frobOnPlacesGeomLevel k 1 data hKr (P.redFst W) = P.redSnd W
      rw [h1, h2, frobOnPlacesGeomLevel_charLGeomPlaceOfPoint k data hKr]
    · change frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.redFst W))
        ≠ P.redFst W
      rw [h1, frobOnPlacesGeomLevel_charLGeomPlaceOfPoint k data hKr,
        frobOnPlacesGeomLevel_charLGeomPlaceOfPoint k data hKr, ← pow_mul]
      exact fun h => ha₀ (charLGeomPlaceOfPoint_injective k h)

theorem mapDomain_filter_apply {ι M : Type*} [DecidableEq M] (D : ι →₀ ℤ) (pr : ι → Prop)
    [DecidablePred pr] (g : ι → M) (v : M) :
    Finsupp.mapDomain g (D.filter pr) v = ∑ W ∈ D.support.filter (fun W => pr W ∧ g W = v), D W := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finsupp.support_filter]
  simp only [Finsupp.single_apply, Finsupp.filter_apply]
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ => ?_
  by_cases h1 : pr W <;> by_cases h2 : g W = v <;> simp [h1, h2]

theorem sum_eq_sum_support_filter (r : k →₀ ℤ) (T : Finset k) (cond : k → Prop) [DecidablePred cond]
    (hT : ∀ a, a ∈ T ↔ cond a) : ∑ a ∈ T, r a = ∑ a ∈ r.support.filter cond, r a := by
  symm
  apply Finset.sum_subset
  · intro a ha; rw [Finset.mem_filter] at ha; exact (hT a).mpr ha.2
  · intro a haT hane
    by_contra h
    exact hane (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr h, (hT a).mp haT⟩)

theorem mem_roots_toFinset_iff_of_X {l c : k} (a : k) :
    a ∈ (C l * X ^ q + X - C c : k[X]).roots.toFinset ↔ a + l * a ^ q = c := by
  have hp : (C l * X ^ q + X - C c : k[X]) ≠ 0 := by
    intro h
    have := congrArg (fun p : k[X] => p.coeff 1) h
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X_one, coeff_C_succ, coeff_zero,
      sub_zero] at this
    have hq1 : (1 : ℕ) ≠ q := (Fact.out : q.Prime).one_lt.ne
    rw [if_neg hq1, mul_zero, zero_add] at this
    exact one_ne_zero this
  rw [Multiset.mem_toFinset, mem_roots hp, IsRoot.def]
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  constructor <;> intro h <;> linear_combination h

theorem mem_roots_toFinset_iff_of_X_pow {l c : k} (b : k) :
    b ∈ (X ^ q + C l * X - C c : k[X]).roots.toFinset ↔ b ^ q + l * b = c := by
  have hp : (X ^ q + C l * X - C c : k[X]) ≠ 0 := by
    intro h
    have := congrArg (fun p : k[X] => p.coeff q) h
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero,
      if_pos rfl] at this
    have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
    have hq1 : (1 : ℕ) ≠ q := (Fact.out : q.Prime).one_lt.ne
    rw [if_neg hq1, if_neg hq0, mul_zero, add_zero, sub_zero] at this
    exact one_ne_zero this
  rw [Multiset.mem_toFinset, mem_roots hp, IsRoot.def]
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  constructor <;> intro h <;> linear_combination h

end Main

section Assembly

open ModularCurve.PlaceSpecialization Finset

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

local notation "Qb" => AlgebraicClosure ℚ
local notation "FF" => modularFunctionFieldBar (1 * q)
local notation "Fb" => modularFunctionFieldC k 1
local notation "Pt" => charLGeomPlaceOfPoint k

theorem infinite_range_red (R : LevelOneProlongationPair P) : (Set.range (red : A → k)).Infinite := by
  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : Infinite (IsLocalRing.ResidueField A) := inferInstance
  have hsub : Set.range R.redBar ⊆ Set.range (red : A → k) := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective t
    exact ⟨a, (R.redBar_residue a).symm⟩
  exact (Set.infinite_range_of_injective R.redBar.injective).mono hsub

set_option maxHeartbeats 6400000 in

theorem divisorLawFst_of_pencil (R : LevelOneProlongationPair P) : R.DivisorLawFst := by
  classical
  haveI : HasPrincipalDivisors k Fb := hasPrincipalDivisors_charLOne k
  intro f h₁ h₂ hu₁ hu₂ D hD v hv
  have hres₁ : R.residue₁ ⟨f, h₁⟩ ≠ 0 := fun h0 => hu₁ (R.ι.injective (by
    rw [map_zero]; rw [LevelOneProlongationPair.residue₁_apply] at h0; exact h0))
  have hres₂ : R.residue₂ ⟨f, h₂⟩ ≠ 0 := fun h0 => hu₂ (R.ι.injective (by
    rw [map_zero]; rw [LevelOneProlongationPair.residue₂_apply] at h0; exact h0))
  by_cases hrat : ∃ a₀, v = Pt a₀
  · obtain ⟨a₀, rfl⟩ := hrat
    have ha₀ : a₀ ^ (q * q) ≠ a₀ := fun h => hv (by
      rw [frobOnPlacesGeomLevel_charLGeomPlaceOfPoint k data hKr,
        frobOnPlacesGeomLevel_charLGeomPlaceOfPoint k data hKr, ← pow_mul, h])

    obtain ⟨D₁, hD₁, -⟩ := HasPrincipalDivisors.exists_divisor (K := k) (R.residue₁ ⟨f, h₁⟩) hres₁
    obtain ⟨D₂, hD₂, -⟩ := HasPrincipalDivisors.exists_divisor (K := k) (R.residue₂ ⟨f, h₂⟩) hres₂
    let r₁ : k →₀ ℤ := D₁.comapDomain Pt (charLGeomPlaceOfPoint_injective k).injOn
    let r₂ : k →₀ ℤ := D₂.comapDomain Pt (charLGeomPlaceOfPoint_injective k).injOn
    have hr₁ : ∀ a, r₁ a = (Pt a).ord (R.residue₁ ⟨f, h₁⟩) := fun a => by
      rw [Finsupp.comapDomain_apply, hD₁]
    have hr₂ : ∀ b, r₂ b = (Pt b).ord (R.residue₂ ⟨f, h₂⟩) := fun b => by
      rw [Finsupp.comapDomain_apply, hD₂]

    have hT : ∀ l ∈ Set.range (red : A → k), ∀ c : k,
        (∑ W ∈ D.support.filter (fun W => IsFin (q := q) (A := A) W ∧
            aOf (q := q) (red := red) W + l * bOf (q := q) (red := red) W = c), D W)
          = (∑ x ∈ r₁.support.filter (fun x => x + l * x ^ q = c), r₁ x)
            + (∑ y ∈ r₂.support.filter (fun y => y ^ q + l * y = c), r₂ y) := by
      rintro l ⟨μ₀, hμ₀⟩ c

      let μ : A := if red μ₀ = 0 then 0 else μ₀
      have hμl : red μ = l := by
        simp only [μ]; split_ifs with h
        · rw [map_zero, ← hμ₀, h]
        · exact hμ₀
      have hμ : red μ ≠ 0 ∨ μ = 0 := by
        simp only [μ]; split_ifs with h
        · exact Or.inr rfl
        · exact Or.inl h
      have hTP := LevelOneProlongationPair.sum_ord_pencil_eq R f h₁ h₂ hu₁ hu₂ D hD μ hμ c

      have eL : (D.support.filter fun W => ∃ x y : A, red x + red μ * red y = c ∧
            0 < W.ord (jFun (q := q) - algebraMap _ _ (x : Qb)) ∧
            0 < W.ord (jqFun (q := q) - algebraMap _ _ (y : Qb))).sum D
          = ∑ W ∈ D.support.filter (fun W => IsFin (q := q) (A := A) W ∧
            aOf (q := q) (red := red) W + l * bOf (q := q) (red := red) W = c), D W := by
        refine Finset.sum_congr (Finset.filter_congr fun W _ => ?_) fun _ _ => rfl
        constructor
        · rintro ⟨x, y, hc, hx, hy⟩
          refine ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, ?_⟩
          rw [aOf_eq P hx, bOf_eq P hy, ← hμl]; exact hc
        · rintro ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hc⟩
          refine ⟨x, y, ?_, hx, hy⟩
          rw [hμl, ← aOf_eq P hx, ← bOf_eq P hy]; exact hc

      have eR1 : ((C (red μ) * X ^ q + X - C c : k[X]).roots.toFinset.sum
            fun a => (Pt a).ord (R.residue₁ ⟨f, h₁⟩))
          = ∑ x ∈ r₁.support.filter (fun x => x + l * x ^ q = c), r₁ x := by
        rw [← sum_eq_sum_support_filter r₁ ((C (red μ) * X ^ q + X - C c : k[X]).roots.toFinset)
          (fun x => x + l * x ^ q = c)
          (fun a => by rw [mem_roots_toFinset_iff_of_X, hμl])]
        exact Finset.sum_congr rfl fun a _ => (hr₁ a).symm
      have eR2 : ((X ^ q + C (red μ) * X - C c : k[X]).roots.toFinset.sum
            fun b => (Pt b).ord (R.residue₂ ⟨f, h₂⟩))
          = ∑ y ∈ r₂.support.filter (fun y => y ^ q + l * y = c), r₂ y := by
        rw [← sum_eq_sum_support_filter r₂ ((X ^ q + C (red μ) * X - C c : k[X]).roots.toFinset)
          (fun y => y ^ q + l * y = c)
          (fun b => by rw [mem_roots_toFinset_iff_of_X_pow, hμl])]
        exact Finset.sum_congr rfl fun b _ => (hr₂ b).symm
      rw [← eL, ← eR1, ← eR2]
      exact hTP
    have hdich : ∀ W ∈ D.support, IsFin (q := q) (A := A) W →
        bOf (q := q) (red := red) W = aOf (q := q) (red := red) W ^ q ∨
          aOf (q := q) (red := red) W = bOf (q := q) (red := red) W ^ q :=
      fun W _ hW => bOf_eq_pow_or P hW
    have hmain := Ws25.Isolation.sum_filter_eq_of_forall_pencil q D.support (⇑D)
      (IsFin (q := q) (A := A)) (aOf (q := q) (red := red)) (bOf (q := q) (red := red)) hdich r₁ r₂
      (Set.range (red : A → k)) (infinite_range_red R) hT a₀ ha₀

    rw [mapDomain_filter_apply, ← hr₁ a₀, ← hmain]
    refine Finset.sum_congr (Finset.filter_congr fun W _ => ?_) fun _ _ => rfl
    exact isStrictTypeOne_and_redFst_eq_iff P ha₀
  ·
    have hvinf : v ≠ charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := fun h => hv (by
      rw [h, frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty,
        frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty])
    rw [mapDomain_filter_apply, Finset.sum_eq_zero, LevelOneProlongationPair.ord_residue_fst_eq_zero_of_forall_ne
      R ⟨f, h₁⟩ v (fun a h => hrat ⟨a, h⟩) hvinf]
    intro W hW
    exfalso
    obtain ⟨-, -, hWv⟩ := Finset.mem_filter.mp hW
    by_cases hj : ∃ x : A, JVal (q := q) W x
    · obtain ⟨x, hx⟩ := hj
      exact hrat ⟨red x, by rw [← hWv, redFst_eq_of_jVal P hx]⟩
    · apply hvinf
      rw [← hWv]
      exact redFst_eq_placeInfty_of_forall_ord_le_zero' P W (fun x => not_lt.mp (fun h => hj ⟨x, h⟩))

end Assembly

end Ws25.PSFst

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair) :
    R.DivisorLawFst :=
  Ws25.PSFst.divisorLawFst_of_pencil R

end

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_divisorLawFst
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_divisorLawFst (solution)
