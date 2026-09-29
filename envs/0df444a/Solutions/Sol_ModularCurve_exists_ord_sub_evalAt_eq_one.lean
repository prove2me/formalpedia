-- Prove2me | solution 1 for ModularCurve.exists_ord_sub_evalAt_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/32aa2836-8469-58bf-8b55-6d31a858be34

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_ModularCurve_JZero_exists_regVal_chord_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_ord_add_embDivisor_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ord_sub_evalAt_eq_one
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open AlgebraicCurve ModularCurve

noncomputable section

namespace P2MJ3

section Generic

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

theorem ord_nonneg_of_mem (v : Place (AlgebraicClosure ℚ) F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    0 ≤ v.ord f :=
  ((v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem hf)).resolve_left hf0

theorem evalAt_ne_zero_iff_ord_eq_zero (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) : v.evalAt f ≠ 0 ↔ v.ord f = 0 := by
  constructor
  · intro hne
    by_contra h0
    have hpos : 0 < v.ord f := lt_of_le_of_ne (ord_nonneg_of_mem v hf hf0) (Ne.symm h0)
    apply hne
    have hnu : ¬IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
      rintro ⟨u, hu⟩
      have h := v.ord_coe_unit u
      rw [hu] at h
      change v.ord f = 0 at h
      omega
    have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0 := by
      by_contra h; exact hnu ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp h)
    rw [v.evalAt_of_mem hf, hres, ← map_zero (algebraMap (AlgebraicClosure ℚ) v.ResidueField),
      v.residueInv_algebraMap]
  · exact fun h => v.evalAt_ne_zero_of_ord_eq_zero hv hf0 h

theorem ord_pos_of_evalAt_eq_zero (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) (h0 : v.evalAt f = 0) : 0 < v.ord f := by
  rcases (ord_nonneg_of_mem v hf hf0).lt_or_eq with h | h
  · exact h
  · exact absurd h0 ((evalAt_ne_zero_iff_ord_eq_zero v hv hf hf0).mpr h.symm)

theorem ord_algebraMap (v : Place (AlgebraicClosure ℚ) F) {c : AlgebraicClosure ℚ} (hc : c ≠ 0) :
    v.ord (algebraMap (AlgebraicClosure ℚ) F c) = 0 := by
  have h1 := ord_nonneg_of_mem v (v.algebraMap_mem' c) (by simpa using hc)
  have h2 := ord_nonneg_of_mem v (v.algebraMap_mem' c⁻¹) (by simpa using hc)
  rw [map_inv₀, v.ord_inv] at h2
  omega

theorem adicValuation_sub_evalAt_le (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    v.adicValuation (f - algebraMap (AlgebraicClosure ℚ) F (v.evalAt f)) ≤ WithZero.exp (-1 : ℤ) := by
  rw [v.adicValuation_le_exp_iff]
  set d := f - algebraMap (AlgebraicClosure ℚ) F (v.evalAt f) with hd
  rcases eq_or_ne d 0 with h0 | h0
  · exact Or.inl h0
  · right
    have hdm : d ∈ v.toValuationSubring := sub_mem hf (v.algebraMap_mem' _)
    have hval : v.evalAt d = 0 := by
      have hsum : d = f + algebraMap (AlgebraicClosure ℚ) F (-(v.evalAt f)) := by rw [hd, map_neg, sub_eq_add_neg]
      have hcm : algebraMap (AlgebraicClosure ℚ) F (-(v.evalAt f)) ∈ v.toValuationSubring := v.algebraMap_mem' _
      have hadd : v.evalAt (f + algebraMap (AlgebraicClosure ℚ) F (-(v.evalAt f)))
          = v.evalAt f + v.evalAt (algebraMap (AlgebraicClosure ℚ) F (-(v.evalAt f))) := by
        apply v.algebraMap_residueField_injective
        rw [map_add, v.algebraMap_evalAt hv (add_mem hf hcm), v.algebraMap_evalAt hv hf,
          v.algebraMap_evalAt hv hcm, ← map_add]
        rfl
      rw [hsum, hadd, v.evalAt_algebraMap_eq, add_neg_cancel]
    have := ord_pos_of_evalAt_eq_zero v hv hdm h0 hval
    first | simpa using this | exact this | (simpa [Int.pos_iff_one_le] using this) | omega

theorem chord_identity {xi xj ai aj q : AlgebraicClosure ℚ} (si sj : F) (hxi : xi = ai * q) (hxj : xj = aj * q) :
    algebraMap (AlgebraicClosure ℚ) F q *
        (algebraMap (AlgebraicClosure ℚ) F ai * (sj - algebraMap (AlgebraicClosure ℚ) F aj)
          - algebraMap (AlgebraicClosure ℚ) F aj * (si - algebraMap (AlgebraicClosure ℚ) F ai))
      = xi • sj - xj • si := by
  rw [Algebra.smul_def, Algebra.smul_def, hxi, hxj, map_mul, map_mul]
  ring

end Generic

section Bar

variable {N : ℕ} [NeZero N] {r : ℕ}

theorem embDivisor_apply_of_ne {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hw : w ≠ cuspInftyBar N) :
    embDivisor N w = 0 := by
  classical
  rw [ModularCurve.embDivisor, Finsupp.smul_apply, Finsupp.single_apply, if_neg (fun h => hw h.symm), smul_zero]

variable {s : Fin r → modularFunctionFieldBar N}

theorem emb_ne_zero (hs : IsEmbBasis N s) (i : Fin r) : s i ≠ 0 := hs.1.ne_zero i

theorem emb_mem (hs : IsEmbBasis N s) (i : Fin r) : s i ∈ riemannRochSpace (embDivisor N) := by
  rw [← hs.2]; exact Submodule.subset_span ⟨i, rfl⟩

theorem emb_regular (hs : IsEmbBasis N s) {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hw : w ≠ cuspInftyBar N) (i : Fin r) : s i ∈ w.toValuationSubring := by
  have h := (mem_riemannRochSpace_iff.mp (emb_mem hs i) w).resolve_left (emb_ne_zero hs i)
  rw [embDivisor_apply_of_ne hw, neg_zero] at h
  exact w.mem_toValuationSubring_of_ord_nonneg_alt (emb_ne_zero hs i) h

theorem ord_pivot_eq_zero (hr : 0 < r) (hs : IsEmbBasis N s) {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hw : w ≠ cuspInftyBar N) : w.ord (s (pivotIndex s w hr)) = 0 := by
  classical
  have hex : ∃ i : Fin r, ∀ j : Fin r, w.ord (s i) ≤ w.ord (s j) := by
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    exact Finite.exists_min fun i => w.ord (s i)
  have hpiv : ∀ j, w.ord (s (pivotIndex s w hr)) ≤ w.ord (s j) := by
    unfold pivotIndex; rw [dif_pos hex]; exact Classical.choose_spec hex
  have hnn : 0 ≤ w.ord (s (pivotIndex s w hr)) :=
    ord_nonneg_of_mem w (emb_regular hs hw _) (emb_ne_zero hs _)
  obtain ⟨i₀, hi₀⟩ := ModularCurve.exists_ord_add_embDivisor_eq_zero N s hs w
  rw [embDivisor_apply_of_ne hw, add_zero] at hi₀
  have := hpiv i₀
  omega

theorem main (hs : IsEmbBasis N s) (R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hR : R ≠ cuspInftyBar N) :
    ∃ i, s i ∈ R.toValuationSubring ∧
      R.ord (s i - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (R.evalAt (s i))) = 1 := by
  classical

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R.toValuationSubring
  set t : modularFunctionFieldBar N := (π : modularFunctionFieldBar N) with ht
  have hordt : R.ord t = 1 := R.ord_coe_irreducible hπ
  have ht0 : t ≠ 0 := by intro h; rw [h] at hordt; simp at hordt

  obtain ⟨⟨i, j⟩, hne⟩ := ModularCurve.JZero.exists_regVal_chord_ne_zero N s hs R t hordt
  have hr : 0 < r := Fin.pos i
  have hrat : R.IsRational :=
    (AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField R).1 (deg_eq_one_modularFunctionFieldBar N R)
  set p₀ := pivotIndex s R hr with hp₀
  set g : modularFunctionFieldBar N := evalVec s R i • s j - evalVec s R j • s i with hg

  have hne' : R.evalAt (g * (s p₀)⁻¹ ^ 1 * t⁻¹ ^ 1) ≠ 0 := by
    unfold regVal at hne; rw [dif_pos hr] at hne; exact hne
  set w : modularFunctionFieldBar N := g * (s p₀)⁻¹ ^ 1 * t⁻¹ ^ 1 with hw
  have hwmem : w ∈ R.toValuationSubring := by
    by_contra hmem; apply hne'; rw [Place.evalAt, dif_neg hmem]
  have hw0 : w ≠ 0 := by
    intro h0; apply hne'
    rw [h0, ← map_zero (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), R.evalAt_algebraMap_eq]
  have hg0 : g ≠ 0 := by
    intro h0; apply hw0; rw [hw, h0, zero_mul, zero_mul]
  have hordw : R.ord w = 0 := (evalAt_ne_zero_iff_ord_eq_zero R hrat hwmem hw0).mp hne'
  have hpiv0 : R.ord (s p₀) = 0 := ord_pivot_eq_zero hr hs hR
  have hsp0 : s p₀ ≠ 0 := emb_ne_zero hs p₀
  have hordg : R.ord g = 1 := by
    rw [hw, pow_one, pow_one, R.ord_mul (mul_ne_zero hg0 (inv_ne_zero hsp0)) (inv_ne_zero ht0),
      R.ord_mul hg0 (inv_ne_zero hsp0), R.ord_inv, R.ord_inv, hpiv0, hordt] at hordw
    omega

  have hreg : ∀ m, s m ∈ R.toValuationSubring := fun m => emb_regular hs hR m
  have hinvmem : (s p₀)⁻¹ ∈ R.toValuationSubring :=
    R.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hsp0) (by rw [R.ord_inv, hpiv0, neg_zero])
  set q : AlgebraicClosure ℚ := R.evalAt (s p₀)⁻¹ with hq
  have hx : ∀ m, evalVec s R m = R.evalAt (s m) * q := by
    intro m
    simp only [evalVec, dif_pos hr]
    rw [← hp₀, R.evalAt_mul_of_mem hrat (hreg m) hinvmem]
  have hq0 : q ≠ 0 := by
    have h1 : R.evalAt (s p₀ * (s p₀)⁻¹) = 1 := by rw [mul_inv_cancel₀ hsp0, R.evalAt_one]
    rw [R.evalAt_mul_of_mem hrat (hreg p₀) hinvmem, ← hq] at h1
    intro h0; rw [h0, mul_zero] at h1; exact zero_ne_one h1

  set D : modularFunctionFieldBar N :=
    algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (R.evalAt (s i))
        * (s j - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (R.evalAt (s j)))
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (R.evalAt (s j))
        * (s i - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (R.evalAt (s i))) with hDdef
  have hqD : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) q * D = g :=
    chord_identity (s i) (s j) (hx i) (hx j)
  have hD0 : D ≠ 0 := by
    intro h0; apply hg0; rw [← hqD, h0, mul_zero]
  have hordD : R.ord D = 1 := by
    have := congrArg R.ord hqD
    rw [R.ord_mul (by simpa using hq0) hD0, ord_algebraMap R hq0, hordg] at this
    omega

  by_contra hnone
  push Not at hnone
  have hsmall : ∀ m, R.ord (s m - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (R.evalAt (s m))) ≠ 1 →
      R.adicValuation (s m - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (R.evalAt (s m)))
        ≤ WithZero.exp (-2 : ℤ) := by
    intro m hm1
    have h1 := adicValuation_sub_evalAt_le R hrat (hreg m)
    rw [R.adicValuation_le_exp_iff] at h1 ⊢
    rcases h1 with h0 | h1
    · exact Or.inl h0
    · right; change R.ord _ ≠ 1 at hm1; omega
  have hi := hsmall i (hnone i (hreg i))
  have hj := hsmall j (hnone j (hreg j))
  have hterm : ∀ (c : AlgebraicClosure ℚ) (u : modularFunctionFieldBar N),
      R.adicValuation u ≤ WithZero.exp (-2 : ℤ) →
      R.adicValuation (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c * u) ≤ WithZero.exp (-2 : ℤ) := by
    intro c u hu
    rw [map_mul]
    calc R.adicValuation (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) * R.adicValuation u
        ≤ 1 * WithZero.exp (-2 : ℤ) := mul_le_mul' (R.adicValuation_algebraMap_le_one c) hu
      _ = WithZero.exp (-2 : ℤ) := one_mul _
  have hDle : R.adicValuation D ≤ WithZero.exp (-2 : ℤ) := by
    rw [hDdef]
    exact (Valuation.map_sub _ _ _).trans (max_le (hterm _ _ hj) (hterm _ _ hi))
  have hDval : R.adicValuation D = WithZero.exp (-1 : ℤ) := by
    rw [R.adicValuation_eq_exp_neg_ord hD0, hordD]
  rw [hDval, WithZero.exp_le_exp] at hDle
  omega

end Bar

end P2MJ3

end

open AlgebraicCurve ModularCurve in

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hR : R ≠ cuspInftyBar N) :
    ∃ i, s i ∈ R.toValuationSubring ∧
      R.ord (s i - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (R.evalAt (s i))) = 1 :=
  P2MJ3.main hs R hR

end S_ModularCurve_exists_ord_sub_evalAt_eq_one
end P2MW
export P2MW.S_ModularCurve_exists_ord_sub_evalAt_eq_one (solution)
