-- Prove2me | solution 1 for ModularCurve.ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/8397734c-505e-5cd4-9df9-e25e4b0f2d5a

import Mathlib
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_divisorLawFst_oneSided
import Theorems.Thm_ModularCurve_placeSpecialization_exists_level_one_residueField
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_levelOneProlongationPair
import Theorems.Thm_ModularCurve_exists_kroneckerCongruence_of_prime
import Theorems.Thm_ModularCurve_heckeAlphaBarIntegral_of_prime
import Theorems.Thm_ModularCurve_heckeBetaBarIntegral_of_prime
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_placeInfty_of_forall_ord_le_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_sp_eq_placeInfty_of_forall_ord_le_zero
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_X_sub_C
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_ne
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄"
p2m_attr_erase "simp" "compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_ne.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective jqModC modularFunctionFieldC jqModC_mem qExpand jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full transcendental_jqModC ssJSet CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange modularFunctionFieldBar PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.jFun PlaceSpecialization.jqFun PlaceSpecialization.LevelOneProlongationPair.residue₁_apply PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence coeffMap_jqModC coeffMap_qExpand PlaceSpecialization.LevelOneProlongationPair.divisorLawFst_oneSided placeSpecialization_exists_level_one_residueField exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime hasPrincipalDivisors_modularFunctionFieldBar_unconditional frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceOfPoint_of_ord_pos"
p2m_open "ModularCurve"
namespace C4a

theorem ratFuncEquivCharLOneC_X (k : Type*) [Field k] :
    ratFuncEquivCharLOneC k RatFunc.X = ⟨jqModC k, jqModC_mem k 1⟩ := by
  apply Subtype.ext
  simp only [ratFuncEquivCharLOneC, AlgEquiv.trans_apply]
  exact RatFunc.algEquivOfTranscendental_X (f := jqModC k) (h := transcendental_jqModC k)

theorem ord_charLGeomPlaceEquiv (k : Type*) [Field k] (v₀ : Place k (RatFunc k)) (f : RatFunc k) :
    (charLGeomPlaceEquiv k v₀).ord (ratFuncEquivCharLOneC k f) = v₀.ord f :=
  Place.ord_congrRingEquiv (ratFuncEquivCharLOneC k).toRingEquiv
    (fun a => (ratFuncEquivCharLOneC k).commutes a) v₀ f

theorem ratFuncEquivCharLOneC_algebraMap (K : Type*) [Field K] (p : Polynomial K) :
    ratFuncEquivCharLOneC K (algebraMap (Polynomial K) (RatFunc K) p)
      = Polynomial.aeval (⟨jqModC K, jqModC_mem K 1⟩ : ↥(modularFunctionFieldC K 1)) p := by
  have h1 : algebraMap (Polynomial K) (RatFunc K) p = Polynomial.aeval (RatFunc.X : RatFunc K) p := by
    rw [← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  rw [h1]
  change (ratFuncEquivCharLOneC K : RatFunc K →ₐ[K] ↥(modularFunctionFieldC K 1)) (Polynomial.aeval RatFunc.X p) = _
  rw [← Polynomial.aeval_algHom_apply]
  have h2 : (ratFuncEquivCharLOneC K : RatFunc K →ₐ[K] ↥(modularFunctionFieldC K 1)) RatFunc.X = ⟨jqModC K, jqModC_mem K 1⟩ :=
    ratFuncEquivCharLOneC_X K
  rw [h2]

theorem coe_aeval_jC (K : Type*) [Field K] (p : Polynomial K) :
    ((Polynomial.aeval (⟨jqModC K, jqModC_mem K 1⟩ : ↥(modularFunctionFieldC K 1)) p :
        ↥(modularFunctionFieldC K 1)) : LaurentSeries K) = Polynomial.aeval (jqModC K) p :=
  (Polynomial.aeval_algHom_apply (modularFunctionFieldC K 1).val
    (⟨jqModC K, jqModC_mem K 1⟩ : ↥(modularFunctionFieldC K 1)) p).symm

theorem ord_charLGeomPlaceOfPoint_aeval (K : Type*) [Field K] (b : K) (p : Polynomial K) (hp : p ≠ 0) :
    (charLGeomPlaceOfPoint K b).ord (Polynomial.aeval (⟨jqModC K, jqModC_mem K 1⟩ : ↥(modularFunctionFieldC K 1)) p)
      = (Polynomial.rootMultiplicity b p : ℤ) := by
  rw [← ratFuncEquivCharLOneC_algebraMap]
  show (charLGeomPlaceEquiv K (RationalFunctionField.placeOfPoint K b)).ord _ = _
  rw [ord_charLGeomPlaceEquiv]
  exact RationalFunctionField.ord_placeOfPoint_algebraMap b hp

theorem coeffMap_aeval_jqModC {k₀ k : Type*} [Field k₀] [Field k] (θ : k₀ →+* k) (p : Polynomial k₀) :
    coeffMap θ (Polynomial.aeval (jqModC k₀) p) = Polynomial.aeval (jqModC k) (p.map θ) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂, coeffMap_jqModC]
  congr 1
  ext c
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem ord_transport {k₀ k : Type*} [Field k₀] [Field k] (θ : k₀ →+* k)
    (y : ↥(modularFunctionFieldC k₀ 1)) (hy0 : y ≠ 0) (z : ↥(modularFunctionFieldC k 1))
    (hz : (z : LaurentSeries k) = coeffMap θ (y : LaurentSeries k₀)) :
    (∀ a₀ : k₀, (charLGeomPlaceOfPoint k (θ a₀)).ord z = (charLGeomPlaceOfPoint k₀ a₀).ord y) ∧
    (IsAlgClosed k₀ → ∀ a : k, (∀ a₀, θ a₀ ≠ a) → (charLGeomPlaceOfPoint k a).ord z = 0) := by
  classical

  obtain ⟨r, hr⟩ := (ratFuncEquivCharLOneC k₀).surjective y
  set p := r.num with hp
  set d := r.denom with hd
  have hd0 : d ≠ 0 := RatFunc.denom_ne_zero r
  have hr0 : r ≠ 0 := by rintro rfl; exact hy0 (by rw [← hr, map_zero])
  have hp0 : p ≠ 0 := RatFunc.num_ne_zero hr0
  set J₀ : ↥(modularFunctionFieldC k₀ 1) := ⟨jqModC k₀, jqModC_mem k₀ 1⟩ with hJ₀
  set J : ↥(modularFunctionFieldC k 1) := ⟨jqModC k, jqModC_mem k 1⟩ with hJ
  have hyeq : y = Polynomial.aeval J₀ p / Polynomial.aeval J₀ d := by
    rw [← hr, ← RatFunc.num_div_denom r, map_div₀, ratFuncEquivCharLOneC_algebraMap, ratFuncEquivCharLOneC_algebraMap]
  have hed0 : Polynomial.aeval J₀ d ≠ 0 := by
    rw [← ratFuncEquivCharLOneC_algebraMap]
    exact (map_ne_zero_iff _ (ratFuncEquivCharLOneC k₀).injective).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k₀) (RatFunc k₀))).mpr hd0)
  have hep0 : Polynomial.aeval J₀ p ≠ 0 := by
    rw [← ratFuncEquivCharLOneC_algebraMap]
    exact (map_ne_zero_iff _ (ratFuncEquivCharLOneC k₀).injective).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k₀) (RatFunc k₀))).mpr hp0)
  have hpθ0 : p.map θ ≠ 0 := (Polynomial.map_ne_zero_iff θ.injective).mpr hp0
  have hdθ0 : d.map θ ≠ 0 := (Polynomial.map_ne_zero_iff θ.injective).mpr hd0
  have heθd0 : Polynomial.aeval J (d.map θ) ≠ 0 := by
    rw [← ratFuncEquivCharLOneC_algebraMap]
    exact (map_ne_zero_iff _ (ratFuncEquivCharLOneC k).injective).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k) (RatFunc k))).mpr hdθ0)
  have heθp0 : Polynomial.aeval J (p.map θ) ≠ 0 := by
    rw [← ratFuncEquivCharLOneC_algebraMap]
    exact (map_ne_zero_iff _ (ratFuncEquivCharLOneC k).injective).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k) (RatFunc k))).mpr hpθ0)

  have hzeq : z = Polynomial.aeval J (p.map θ) / Polynomial.aeval J (d.map θ) := by
    apply Subtype.ext
    rw [hz, hyeq]
    show coeffMap θ (((Polynomial.aeval J₀ p / Polynomial.aeval J₀ d : ↥(modularFunctionFieldC k₀ 1)) : LaurentSeries k₀))
      = ((Polynomial.aeval J (p.map θ) / Polynomial.aeval J (d.map θ) : ↥(modularFunctionFieldC k 1)) : LaurentSeries k)
    push_cast
    rw [map_div₀, coe_aeval_jC, coe_aeval_jC, coe_aeval_jC, coe_aeval_jC, coeffMap_aeval_jqModC, coeffMap_aeval_jqModC]

  have hordz : ∀ b : k, (charLGeomPlaceOfPoint k b).ord z
      = (Polynomial.rootMultiplicity b (p.map θ) : ℤ) - (Polynomial.rootMultiplicity b (d.map θ) : ℤ) := by
    intro b
    rw [hzeq, div_eq_mul_inv, Place.ord_mul _ heθp0 (inv_ne_zero heθd0), Place.ord_inv,
      ord_charLGeomPlaceOfPoint_aeval k b _ hpθ0, ord_charLGeomPlaceOfPoint_aeval k b _ hdθ0]
    ring
  have hordy : ∀ b : k₀, (charLGeomPlaceOfPoint k₀ b).ord y
      = (Polynomial.rootMultiplicity b p : ℤ) - (Polynomial.rootMultiplicity b d : ℤ) := by
    intro b
    rw [hyeq, div_eq_mul_inv, Place.ord_mul _ hep0 (inv_ne_zero hed0), Place.ord_inv,
      ord_charLGeomPlaceOfPoint_aeval k₀ b _ hp0, ord_charLGeomPlaceOfPoint_aeval k₀ b _ hd0]
    ring
  refine ⟨fun a₀ => ?_, fun hclosed a ha => ?_⟩
  · rw [hordz, hordy, ← Polynomial.eq_rootMultiplicity_map θ.injective, ← Polynomial.eq_rootMultiplicity_map θ.injective]
  · haveI := hclosed
    have hroot : ∀ s : Polynomial k₀, s ≠ 0 → Polynomial.rootMultiplicity a (s.map θ) = 0 := by
      intro s hs
      apply Polynomial.rootMultiplicity_eq_zero
      intro hroot
      have hmem : a ∈ (s.map θ).roots := (Polynomial.mem_roots ((Polynomial.map_ne_zero_iff θ.injective).mpr hs)).mpr hroot
      rw [← Polynomial.roots_map_of_injective_of_card_eq_natDegree θ.injective
        (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits s))] at hmem
      obtain ⟨a₀, -, rfl⟩ := Multiset.mem_map.mp hmem
      exact ha a₀ rfl
    rw [hordz, hroot p hp0, hroot d hd0]
    simp

section RedNat
variable {L : Type*} [Field L] (B : Subring L) {k₀ k : Type*} [Field k₀] [Field k] (red₀ : B →+* k₀) (θ : k₀ →+* k)
  (N : ℕ) [NeZero N]

theorem coeffRed_comp (x : CharPReduction.integralCoeffs B) :
    CharPReduction.coeffRed B (θ.comp red₀) x = coeffMap θ (CharPReduction.coeffRed B red₀ x) := by
  ext n
  rw [CharPReduction.coeffRed_coeff, coeffMap_coeff, CharPReduction.coeffRed_coeff, RingHom.comp_apply]

theorem redRes_comp (s : ↥(CharPReduction.modularRing N B)) :
    CharPReduction.redRes B (θ.comp red₀) (CharPReduction.modularRing N B) (CharPReduction.modularRing_le_integralCoeffs N B) s
      = coeffMap θ (CharPReduction.redRes B red₀ (CharPReduction.modularRing N B) (CharPReduction.modularRing_le_integralCoeffs N B) s) := by
  rw [CharPReduction.redRes_apply, CharPReduction.redRes_apply, coeffRed_comp]

theorem coeffMap_injective_field : Function.Injective (coeffMap (R := k₀) (S := k) θ) := by
  intro x y h
  ext n
  have := congrArg (fun s => HahnSeries.coeff s n) h
  simp only [coeffMap_coeff] at this
  exact θ.injective this

theorem redKer_comp_iff (s : ↥(CharPReduction.modularRing N B)) :
    s ∈ CharPReduction.redKer B (θ.comp red₀) (CharPReduction.modularRing N B) (CharPReduction.modularRing_le_integralCoeffs N B)
      ↔ s ∈ CharPReduction.redKer B red₀ (CharPReduction.modularRing N B) (CharPReduction.modularRing_le_integralCoeffs N B) := by
  rw [CharPReduction.redKer, RingHom.mem_ker, CharPReduction.redKer, RingHom.mem_ker, redRes_comp]
  constructor
  · intro h
    exact coeffMap_injective_field θ (by rw [h, map_zero])
  · intro h; rw [h, map_zero]

theorem mem_modularLocalized_comp_iff (g : LaurentSeries L) :
    g ∈ CharPReduction.modularLocalized N B (θ.comp red₀) ↔ g ∈ CharPReduction.modularLocalized N B red₀ := by
  rw [CharPReduction.modularLocalized, CharPReduction.modularLocalized, CharPReduction.mem_localizedAtKer,
    CharPReduction.mem_localizedAtKer]
  constructor
  · rintro ⟨r, s, hs, e⟩; exact ⟨r, s, fun h => hs ((redKer_comp_iff B red₀ θ N s).mpr h), e⟩
  · rintro ⟨r, s, hs, e⟩; exact ⟨r, s, fun h => hs ((redKer_comp_iff B red₀ θ N s).mp h), e⟩

theorem modularRedLocHom_comp (g : LaurentSeries L) (hg : g ∈ CharPReduction.modularLocalized N B (θ.comp red₀))
    (hg₀ : g ∈ CharPReduction.modularLocalized N B red₀) :
    CharPReduction.modularRedLocHom N B (θ.comp red₀) ⟨g, hg⟩
      = coeffMap θ (CharPReduction.modularRedLocHom N B red₀ ⟨g, hg₀⟩) := by
  obtain ⟨r, s, hs, e⟩ := (CharPReduction.mem_localizedAtKer _ _ _ _).mp hg₀
  have hs' : s ∉ CharPReduction.redKer B (θ.comp red₀) (CharPReduction.modularRing N B) (CharPReduction.modularRing_le_integralCoeffs N B) :=
    fun h => hs ((redKer_comp_iff B red₀ θ N s).mp h)
  have h1 := CharPReduction.redLoc_spec (A := B) (red := θ.comp red₀) (R := CharPReduction.modularRing N B)
    (hR := CharPReduction.modularRing_le_integralCoeffs N B) ⟨g, hg⟩ (r := r) (s := s) e
  have h0 := CharPReduction.redLoc_spec (A := B) (red := red₀) (R := CharPReduction.modularRing N B)
    (hR := CharPReduction.modularRing_le_integralCoeffs N B) ⟨g, hg₀⟩ (r := r) (s := s) e
  have hs0 : CharPReduction.redRes B red₀ (CharPReduction.modularRing N B) (CharPReduction.modularRing_le_integralCoeffs N B) s ≠ 0 :=
    (CharPReduction.notMem_redKer_iff _ _ _ _).mp hs
  have hs1 : CharPReduction.redRes B (θ.comp red₀) (CharPReduction.modularRing N B) (CharPReduction.modularRing_le_integralCoeffs N B) s ≠ 0 :=
    (CharPReduction.notMem_redKer_iff _ _ _ _).mp hs'
  show CharPReduction.redLoc ⟨g, hg⟩ = coeffMap θ (CharPReduction.redLoc ⟨g, hg₀⟩)
  rw [redRes_comp, redRes_comp] at h1
  have h0' := (eq_div_iff hs0).mpr h0
  have h1' := (eq_div_iff hs1).mpr h1
  rw [h1', h0', map_div₀]
  rfl

end RedNat

theorem red_eq_zero_of_mem_maximalIdeal {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    (red : A →+* k) (q : ℕ) [Fact q.Prime] [CharP k q] (τ : A) (hτ : τ ∈ IsLocalRing.maximalIdeal A) : red τ = 0 := by
  have hq : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A q
  have hA : A.LiesOverPrime q := by
    rw [ValuationSubring.LiesOverPrime, ValuationSubring.mem_nonunits_iff]
    have hnu : ¬ IsUnit (⟨(q : AlgebraicClosure ℚ), hq⟩ : A) := by
      intro hu
      have h1 := hu.map red
      have h0 : red ⟨(q : AlgebraicClosure ℚ), hq⟩ = 0 := by
        have : (⟨(q : AlgebraicClosure ℚ), hq⟩ : A) = (q : A) := Subtype.ext (by push_cast; rfl)
        rw [this, map_natCast, CharP.cast_eq_zero]
      rw [h0] at h1
      exact not_isUnit_zero h1
    exact (ValuationSubring.valuation_lt_one_iff A ⟨(q : AlgebraicClosure ℚ), hq⟩).mp
      ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
  exact ValuationSubring.map_eq_zero_of_valuation_lt_one_of_charP A q hA red τ
    ((ValuationSubring.valuation_lt_one_iff A τ).mp hτ)

theorem liesOverPrime_of_ringHom {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) : A.LiesOverPrime q := by
  have hq : (q : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have h := hunit.map red
    rw [map_natCast, CharP.cast_eq_zero] at h
    exact not_isUnit_zero h
  have h := (ValuationSubring.coe_mem_nonunits_iff (A := A)).mpr hq
  have e : (((q : A) : AlgebraicClosure ℚ)) = (q : AlgebraicClosure ℚ) := by norm_cast
  rw [e] at h
  exact h

theorem mapDomain_apply_eq_sum {α β M : Type*} [AddCommMonoid M] [DecidableEq β] (f : α → β) (D : α →₀ M) (v : β) :
    Finsupp.mapDomain f D v = ∑ a ∈ D.support.filter (fun a => f a = v), D a := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : f a = v <;> simp [Finsupp.single_apply, h]

end C4a
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective jqModC modularFunctionFieldC jqModC_mem qExpand jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full transcendental_jqModC ssJSet CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange modularFunctionFieldBar PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.jFun PlaceSpecialization.jqFun PlaceSpecialization.LevelOneProlongationPair.residue₁_apply PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence coeffMap_jqModC coeffMap_qExpand PlaceSpecialization.LevelOneProlongationPair.divisorLawFst_oneSided placeSpecialization_exists_level_one_residueField exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime hasPrincipalDivisors_modularFunctionFieldBar_unconditional frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceOfPoint_of_ord_pos"
p2m_open "ModularCurve"

theorem pinN_G5 {k : Type*} [Field k] {q : ℕ} [Fact q.Prime] [CharP k q]
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data) (a : k) :
    frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceOfPoint k a) = charLGeomPlaceOfPoint k (a ^ q) := by
  letI := Classical.decEq (RatFunc k)
  haveI : CharP ↥(modularFunctionFieldC k 1) q :=
    charP_of_injective_algebraMap (algebraMap k ↥(modularFunctionFieldC k 1)).injective q
  set J : ↥(modularFunctionFieldC k 1) := ⟨jqModC k, jqModC_mem k 1⟩ with hJ

  have hord1 : (charLGeomPlaceOfPoint k a).ord (J - algebraMap k _ a) = 1 := by
    classical
    have e1 : (charLGeomPlaceOfPoint k a).ord (J - algebraMap k _ a)
        = (AlgebraicCurve.RationalFunctionField.placeOfPoint k a).ord
            (RatFunc.X - algebraMap k (RatFunc k) a) := by
      have hJX : (J - algebraMap k _ a) = ratFuncEquivCharLOneC k (RatFunc.X - algebraMap k (RatFunc k) a) := by
        rw [map_sub, ModularCurve.C4a.ratFuncEquivCharLOneC_X, AlgEquiv.commutes]
      rw [hJX, show charLGeomPlaceOfPoint k a
          = charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeOfPoint k a) from rfl,
        ModularCurve.C4a.ord_charLGeomPlaceEquiv]
    rw [e1]
    have hXa : (RatFunc.X - algebraMap k (RatFunc k) a)
        = algebraMap (Polynomial k) (RatFunc k) (Polynomial.X - Polynomial.C a) := by
      rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
    rw [hXa, AlgebraicCurve.RationalFunctionField.ord_X_sub_C k a, Finsupp.add_apply,
      Finsupp.single_eq_same, Finsupp.single_apply, if_neg]
    · rfl
    ·
      intro h
      have hX : (RatFunc.X : RatFunc k) ∈ (AlgebraicCurve.RationalFunctionField.placeOfPoint k a).toValuationSubring := by
        rw [AlgebraicCurve.RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum]
        have := AlgebraicCurve.RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum k
          (AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible k (Polynomial.irreducible_X_sub_C a))
          Polynomial.X
        rwa [RatFunc.algebraMap_X] at this
      rw [← h, AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring,
        Valuation.mem_valuationSubring_iff, RatFunc.inftyValuation.X, ← WithZero.exp_zero,
        WithZero.exp_le_exp] at hX
      norm_num at hX

  have hfrob : frobeniusGeomLevel k 1 data hKr (J - algebraMap k _ (a ^ q))
      = (J - algebraMap k _ a) ^ q := by
    rw [map_sub, hJ, frobeniusGeomLevel_jq, AlgHom.commutes, sub_pow_char, ← map_pow]
  have hJa_mem : (J - algebraMap k _ a) ∈ (charLGeomPlaceOfPoint k a).toValuationSubring :=
    Place.mem_of_ord_nonneg _ (by intro h0; rw [h0, Place.ord_zero] at hord1; exact zero_ne_one hord1)
      (by rw [hord1]; exact zero_le_one)
  apply ModularCurve.eq_charLGeomPlaceOfPoint_of_ord_pos

  have hmem : (J - algebraMap k _ (a ^ q))
      ∈ (frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceOfPoint k a)).toValuationSubring := by
    rw [mem_frobOnPlacesGeomLevel_iff, hfrob]
    exact pow_mem hJa_mem q
  have hne : (J - algebraMap k _ (a ^ q)) ≠ 0 := by
    intro h0
    have := congrArg (frobeniusGeomLevel k 1 data hKr) h0
    rw [hfrob, map_zero] at this
    have h1 := congrArg ((charLGeomPlaceOfPoint k a).ord) this
    rw [← zpow_natCast, Place.ord_zpow, hord1, Place.ord_zero] at h1
    simp at h1
    exact (Fact.out : q.Prime).ne_zero h1
  rcases (Place.ord_nonneg_of_mem _ hmem).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso

    have hinv_mem : (J - algebraMap k _ (a ^ q))⁻¹
        ∈ (frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceOfPoint k a)).toValuationSubring :=
      Place.mem_of_ord_nonneg _ (inv_ne_zero hne) (by rw [Place.ord_inv, ← heq, neg_zero])
    rw [mem_frobOnPlacesGeomLevel_iff, map_inv₀, hfrob] at hinv_mem
    have h2 := Place.ord_nonneg_of_mem _ hinv_mem
    rw [Place.ord_inv, ← zpow_natCast, Place.ord_zpow, hord1, mul_one] at h2
    have : (0 : ℤ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
    omega

end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective jqModC modularFunctionFieldC jqModC_mem qExpand jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full transcendental_jqModC ssJSet CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange modularFunctionFieldBar PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.jFun PlaceSpecialization.jqFun PlaceSpecialization.LevelOneProlongationPair.residue₁_apply PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence coeffMap_jqModC coeffMap_qExpand PlaceSpecialization.LevelOneProlongationPair.divisorLawFst_oneSided placeSpecialization_exists_level_one_residueField exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime hasPrincipalDivisors_modularFunctionFieldBar_unconditional frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceOfPoint_of_ord_pos"
p2m_open "ModularCurve"
namespace C4a

set_option maxHeartbeats 16000000 in
theorem core {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (θ : ResidueField A →+* k)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring (θ.comp (IsLocalRing.residue A)))
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring (θ.comp (IsLocalRing.residue A)) ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1)
    (h₁0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring (θ.comp (IsLocalRing.residue A)) ⟨_, h₁⟩ ≠ 0)
    (a : k) (ha2 : a ^ (q ^ 2) ≠ a)
    (hsupp : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), W.ord f ≠ 0 →
      ¬ ((∃ x : A, (θ.comp (IsLocalRing.residue A)) x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, (θ.comp (IsLocalRing.residue A)) y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    (charLGeomPlaceOfPoint k a).ord
        (⟨CharPReduction.modularRedLocHom (1 * q) A.toSubring (θ.comp (IsLocalRing.residue A)) ⟨_, h₁⟩, h₁F⟩ : modularFunctionFieldC k 1) = 0 := by
  classical
  letI := Classical.decEq (RatFunc (ResidueField A))
  letI := Classical.decEq (ResidueField A)
  haveI : CharP (ResidueField A) q := (RingHom.charP_iff_charP θ q).mpr inferInstance
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  have hA : A.LiesOverPrime q := liesOverPrime_of_ringHom (θ.comp (IsLocalRing.residue A))

  have h₁₀ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring (IsLocalRing.residue A) :=
    (mem_modularLocalized_comp_iff A.toSubring (IsLocalRing.residue A) θ (1 * q) _).mp h₁
  have hT1 := modularRedLocHom_comp A.toSubring (IsLocalRing.residue A) θ (1 * q) _ h₁ h₁₀

  obtain ⟨data, hKr⟩ := ModularCurve.exists_kroneckerCongruence_of_prime q
  have hα := ModularCurve.heckeAlphaBarIntegral_of_prime (AlgebraicClosure ℚ) 1 q
  have hβ := ModularCurve.heckeBetaBarIntegral_of_prime (AlgebraicClosure ℚ) 1 q
  obtain ⟨P⟩ := ModularCurve.placeSpecialization_exists_level_one_residueField q data hKr A hA hα hβ
  obtain ⟨R⟩ := P.exists_levelOneProlongationPair hA
  obtain ⟨hf1, hres⟩ := R.residue₁_eq_modularRedLocHom f h₁₀
  set y : ↥(modularFunctionFieldC (ResidueField A) 1) := R.residue₁ ⟨f, hf1⟩ with hy_def
  have hy : ((y : ↥(modularFunctionFieldC (ResidueField A) 1)) : LaurentSeries (ResidueField A))
      = CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue A) ⟨_, h₁₀⟩ := hres
  have hz : ((⟨CharPReduction.modularRedLocHom (1 * q) A.toSubring (θ.comp (IsLocalRing.residue A)) ⟨_, h₁⟩, h₁F⟩ :
      ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = coeffMap θ (y : LaurentSeries (ResidueField A)) := by
    rw [hy]; exact hT1
  have hy0 : y ≠ 0 := by
    intro h0
    apply h₁0
    rw [hT1, ← hy, h0]
    show coeffMap θ ((0 : ↥(modularFunctionFieldC (ResidueField A) 1)) : LaurentSeries (ResidueField A)) = 0
    rw [ZeroMemClass.coe_zero, map_zero]
  have hfres0 : R.R₁.residue ⟨f, hf1⟩ ≠ 0 := by
    intro h0; apply hy0
    rw [hy_def, ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply, h0, map_zero]
  obtain ⟨hTa, hTb⟩ := ord_transport θ y hy0 _ hz
  by_cases har : ∃ a₀, θ a₀ = a
  · obtain ⟨a₀, rfl⟩ := har
    have ha₀ : a₀ ^ (q ^ 2) ≠ a₀ := fun h => ha2 (by rw [← map_pow, h])

    obtain ⟨D, hD, -⟩ := (ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * q)).exists_divisor f
      (by intro h0; apply hfres0; simp only [h0]; exact map_zero _)
    have hv : frobOnPlacesGeomLevel (ResidueField A) 1 data hKr
        (frobOnPlacesGeomLevel (ResidueField A) 1 data hKr (charLGeomPlaceOfPoint (ResidueField A) a₀))
          ≠ charLGeomPlaceOfPoint (ResidueField A) a₀ := by
      rw [ModularCurve.pinN_G5, ModularCurve.pinN_G5, ← pow_mul, ← sq]
      intro h
      exact ha₀ (charLGeomPlaceOfPoint_injective _ h)
    have hlaw := ModularCurve.PlaceSpecialization.LevelOneProlongationPair.divisorLawFst_oneSided R f hf1 hfres0 D hD _ hv

    have hL : Finsupp.mapDomain P.redFst (D.filter P.IsStrictTypeOne) (charLGeomPlaceOfPoint (ResidueField A) a₀) = 0 := by
      rw [mapDomain_apply_eq_sum]
      refine Finset.sum_eq_zero fun W hW => ?_
      exfalso
      rw [Finset.mem_filter, Finsupp.mem_support_iff, Finsupp.filter_apply] at hW
      obtain ⟨hDW, hWv⟩ := hW
      have hW1 : P.IsStrictTypeOne W := by
        by_contra hn; rw [if_neg hn] at hDW; exact hDW rfl
      rw [if_pos hW1] at hDW
      have hordW : W.ord f ≠ 0 := by rw [← hD]; exact hDW

      have hJα : heckeAlphaBar (AlgebraicClosure ℚ) 1 q (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1)
          = ModularCurve.PlaceSpecialization.jFun (q := q) := Subtype.ext (coe_heckeAlphaBar 1 q _)
      have hJβ : heckeBetaBar (AlgebraicClosure ℚ) 1 q (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1)
          = ModularCurve.PlaceSpecialization.jqFun (q := q) := by
        apply Subtype.ext
        rw [coe_heckeBetaBar]
        show qExpand (AlgebraicClosure ℚ) q (coeffEmb (AlgebraicClosure ℚ) jq) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq)
        simp only [coeffEmb, ModularCurve.coeffMap_qExpand, one_mul]
      have hinf_fix := ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty (ResidueField A) data hKr

      have hx : ∃ x : A, 0 < W.ord (ModularCurve.PlaceSpecialization.jFun (q := q)
          - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ)) := by
        by_contra hno
        push_neg at hno
        have h1 := P.redFst_eq_placeInfty_of_forall_ord_le_zero W hno
        exact hW1.2 (by rw [h1, hinf_fix, hinf_fix])
      obtain ⟨x, hx⟩ := hx
      have hredFst : P.redFst W = charLGeomPlaceOfPoint (ResidueField A) (IsLocalRing.residue A x) :=
        P.redFst_eq_charLGeomPlaceOfPoint_of_ord_pos W x (by rw [hJα]; exact hx)
      have hxa : IsLocalRing.residue A x = a₀ := charLGeomPlaceOfPoint_injective _ (hredFst.symm.trans hWv)

      have hyW : ∃ y₁ : A, 0 < W.ord (ModularCurve.PlaceSpecialization.jqFun (q := q)
          - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (y₁ : AlgebraicClosure ℚ)) := by
        by_contra hno
        push_neg at hno
        have h2 : P.redSnd W = charLGeomPlaceEquiv (ResidueField A) (AlgebraicCurve.RationalFunctionField.placeInfty (ResidueField A)) := by
          refine P.sp_eq_placeInfty_of_forall_ord_le_zero _ fun b => ?_
          have h := hno b
          rw [← hJβ, ← (heckeBetaBar (AlgebraicClosure ℚ) 1 q).commutes (b : AlgebraicClosure ℚ), ← map_sub,
            Place.ord_restrictAlong _ hβ] at h
          have hepos : 0 < (Place.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) W : ℤ) := by
            letI := algebraAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q)
            haveI := isScalarTower_along (heckeBetaBar (AlgebraicClosure ℚ) 1 q)
            haveI := isIntegral_along (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ
            exact_mod_cast Place.ramificationIndex_pos (F := modularFunctionFieldBar 1) W
          by_contra hpos
          push_neg at hpos
          exact absurd h (not_le.mpr (mul_pos hepos hpos))
        have h3 : P.redFst W = charLGeomPlaceEquiv (ResidueField A) (AlgebraicCurve.RationalFunctionField.placeInfty (ResidueField A)) :=
          frobOnPlacesGeomLevel_injective (ResidueField A) 1 data hKr (by rw [hinf_fix]; exact hW1.1.trans h2)
        exact hW1.2 (by rw [h3, hinf_fix, hinf_fix])
      obtain ⟨y₁, hy₁⟩ := hyW
      have hredSnd : P.redSnd W = charLGeomPlaceOfPoint (ResidueField A) (IsLocalRing.residue A y₁) :=
        P.redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos W y₁ (by rw [hJβ]; exact hy₁)
      have hyx : IsLocalRing.residue A y₁ = IsLocalRing.residue A x ^ q := by
        have h := hW1.1
        rw [hredFst, hredSnd, ModularCurve.pinN_G5] at h
        exact (charLGeomPlaceOfPoint_injective _ h).symm
      refine hsupp W hordW ⟨⟨x, ?_, ?_⟩, ⟨y₁, ?_, ?_⟩⟩
      · rw [RingHom.comp_apply, hxa]
      · exact hx
      · rw [RingHom.comp_apply, hyx, map_pow, hxa]
      · exact hy₁
    rw [hTa a₀, ← hlaw, hL]
  · push_neg at har
    exact hTb inferInstance a har

end C4a
end ModularCurve

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1) (h₁0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (a : k) (ha : a ∉ ssJSet q k) (ha2 : a ^ (q ^ 2) ≠ a)
    (hsupp : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), W.ord f ≠ 0 →
      ¬ ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    (charLGeomPlaceOfPoint k a).ord
        (⟨CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩, h₁F⟩ : modularFunctionFieldC k 1) = 0 := by
  have hkerm : ∀ τ : ↥A, τ ∈ IsLocalRing.maximalIdeal ↥A → red τ = 0 := fun τ hτ =>
    ModularCurve.C4a.red_eq_zero_of_mem_maximalIdeal red q τ hτ
  obtain ⟨θ, hθ⟩ : ∃ θ : ResidueField A →+* k, θ.comp (IsLocalRing.residue A) = red :=
    ⟨Ideal.Quotient.lift (IsLocalRing.maximalIdeal ↥A) red hkerm,
      RingHom.ext fun τ => Ideal.Quotient.lift_mk (IsLocalRing.maximalIdeal ↥A) red hkerm⟩
  subst hθ
  exact ModularCurve.C4a.core θ f h₁ h₁F h₁0 a ha2 hsupp

end

end S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_ne
end P2MW
export P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_ne (solution)
