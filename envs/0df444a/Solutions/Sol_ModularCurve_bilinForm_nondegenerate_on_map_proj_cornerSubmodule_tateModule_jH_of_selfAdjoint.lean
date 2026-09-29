-- Prove2me | solution 1 for ModularCurve.bilinForm_nondegenerate_on_map_proj_cornerSubmodule_tateModule_jH_of_selfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/61751c97-9740-5296-a1a5-7e7a606e2433

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_bilinForm_nondegenerate_on_map_proj_cornerSubmodule_tateModule_jH_of_selfAdjoint
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve~coeffEmb_jq IharaLemma"

noncomputable section

namespace EOrth

local notation "Qb" => AlgebraicClosure ℚ

section Divisible

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

omit [NeZero M] in
theorem jq_mem : jq ∈ xHFunctionField M H := by
  have h := intFormRatiosC_subset ℚ (CohCarrier.GammaH M H) (jqModC_mem_intFormRatiosC ℚ (CohCarrier.GammaH M H))
  rw [jqModC_rat] at h
  exact h

def jGen : xHFunctionFieldBar M H :=
  ⟨coeffEmb Qb jq, coeffEmb_mem_laurentBaseChange Qb (jq_mem M H)⟩

theorem coeffEmb_jq (K : Type*) [Field K] [Algebra ℚ K] : coeffEmb K jq = jqModC K := by
  ext k
  rw [coeffEmb_coeff, jqModC_eq_map_intCast (K := K), ← jqModC_rat, jqModC_eq_map_intCast (K := ℚ),
    HahnSeries.map_coeff, HahnSeries.map_coeff]
  simp

omit [NeZero M] in
theorem coe_jGen : ((jGen M H : xHFunctionFieldBar M H) : LaurentSeries Qb) = jqModC Qb :=
  coeffEmb_jq Qb

scoped instance finiteIndex_GammaH : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

theorem transcendental_and_finiteDimensional_jGen :
    Transcendental Qb (jGen M H) ∧
      FiniteDimensional (IntermediateField.adjoin Qb ({jGen M H} : Set (xHFunctionFieldBar M H)))
        (xHFunctionFieldBar M H) :=
  ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
    Qb (CohCarrier.GammaH M H) (translation_mem_GammaH M H) (jGen M H) (coe_jGen M H)

theorem exists_nsmul_eq_jH (n : ℕ) (hn : n ≠ 0) (x : JH M H) : ∃ y : JH M H, n • y = x := by
  obtain ⟨htr, hfd⟩ := transcendental_and_finiteDimensional_jGen M H
  haveI := hfd
  haveI : IsCurveOver Qb (xHFunctionFieldBar M H) :=
    AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental (jGen M H) htr
  exact AlgebraicCurve.Pic0.exists_nsmul_eq Qb (xHFunctionFieldBar M H) ⟨jGen M H, htr, hfd⟩ n hn x

variable {M H} {p : ℕ} [Fact p.Prime]

abbrev Jp (M : ℕ) (H : Subgroup (ZMod M)ˣ) (p : ℕ) : Type _ := ↥(Pic0.torsion Qb (xHFunctionFieldBar M H) p)

def πt (t : TateModule p (JH M H)) : Jp M H p :=
  ⟨TateModule.proj p (JH M H) 1 t,
    Pic0.mem_torsion.mpr (by
      have h := TateModule.torsionBy_proj 1 t
      rwa [pow_one] at h)⟩

omit [NeZero M] in
@[scoped simp] theorem coe_πt (t : TateModule p (JH M H)) : (πt t : JH M H) = TateModule.proj p (JH M H) 1 t := rfl

omit [NeZero M] in
theorem πt_add (t s : TateModule p (JH M H)) : πt (t + s) = πt t + πt s :=
  Subtype.ext (map_add _ t s)

omit [NeZero M] in
theorem πt_zero : πt (0 : TateModule p (JH M H)) = 0 :=
  Subtype.ext (map_zero _)

omit [NeZero M] in

theorem πt_padicInt_smul (r : ℤ_[p]) (t : TateModule p (JH M H)) :
    πt (r • t) = ((r.appr 1 : ℕ) : ℤ) • πt t := by
  apply Subtype.ext
  rw [coe_πt, TateModule.proj_apply, TateModule.smul_apply, AddSubgroupClass.coe_zsmul, coe_πt,
    TateModule.proj_apply]

omit [NeZero M] in
theorem nsmul_coe (x : Jp M H p) : p • (x : JH M H) = 0 := by
  rw [← natCast_zsmul]
  exact Pic0.mem_torsion.mp x.2

theorem exists_πt_eq (z : Jp M H p) : ∃ s : TateModule p (JH M H), πt s = z := by
  have pp : p.Prime := Fact.out
  choose dv hdv using exists_nsmul_eq_jH M H p pp.ne_zero

  let g : ℕ → JH M H := fun k => Nat.rec (z : JH M H) (fun _ y => dv y) k
  have hg0 : g 0 = z := rfl
  have hgs : ∀ k, g (k + 1) = dv (g k) := fun k => rfl
  have hgp : ∀ k, p • g (k + 1) = g k := fun k => by rw [hgs]; exact hdv _
  have hz : p • (z : JH M H) = 0 := nsmul_coe z
  have hkill : ∀ k, p ^ (k + 1) • g k = 0 := by
    intro k
    induction k with
    | zero => rw [zero_add, pow_one, hg0]; exact hz
    | succ k ih => rw [pow_succ, ← smul_smul, hgp]; exact ih

  let f : ℕ → JH M H := fun n => Nat.rec 0 (fun k _ => g k) n
  have hf0 : f 0 = 0 := rfl
  have hfs : ∀ k, f (k + 1) = g k := fun k => rfl
  refine ⟨⟨f, fun n => ⟨?_, ?_⟩⟩, ?_⟩
  · cases n with
    | zero =>
        show ((p ^ 0 : ℕ) : ℤ) • (0 : JH M H) = 0
        rw [smul_zero]
    | succ k =>
        show ((p ^ (k + 1) : ℕ) : ℤ) • g k = 0
        rw [natCast_zsmul]; exact hkill k
  · cases n with
    | zero =>
        show ((p : ℕ) : ℤ) • g 0 = 0
        rw [natCast_zsmul, hg0]; exact hz
    | succ k =>
        show ((p : ℕ) : ℤ) • g (k + 1) = g k
        rw [natCast_zsmul]; exact hgp k
  · exact Subtype.ext rfl

end Divisible

section Adjoint

variable {p : ℕ} [Fact p.Prime] {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {S : Set ℕ}
  {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (JH M H))]
  [IsScalarTower ℤ_[p] 𝕋 (TateModule p (JH M H))]
  (b : LinearMap.BilinForm (ZMod p) (Jp M H p))

def Adj (τ : 𝕋) : Prop :=
  ∀ t s : TateModule p (JH M H), b (πt (τ • t)) (πt s) = b (πt t) (πt (τ • s))

variable (op : CohCarrier.Gen M S → 𝕋)
  (hop : ∀ (g : CohCarrier.Gen M S) (x : TateModule p (JH M H)), op g • x = tateGenOpH M H S p g x)
  (hsa : ∀ (g : CohCarrier.Gen M S) (x y x' y' : Jp M H p),
    (x' : JH M H) = genOpH M H S g (x : JH M H) →
    (y' : JH M H) = genOpH M H S g (y : JH M H) → b x' y = b x y')

include hop hsa in
omit [NeZero M] in
theorem adj_op (g : CohCarrier.Gen M S) : Adj b (op g) := by
  intro t s
  have h1 : ((πt (op g • t) : Jp M H p) : JH M H) = genOpH M H S g (πt t : JH M H) := by
    rw [coe_πt, coe_πt, hop]; rfl
  have h2 : ((πt (op g • s) : Jp M H p) : JH M H) = genOpH M H S g (πt s : JH M H) := by
    rw [coe_πt, coe_πt, hop]; rfl
  exact hsa g (πt t) (πt s) (πt (op g • t)) (πt (op g • s)) h1 h2

omit [NeZero M] in
theorem adj_algebraMap (r : ℤ_[p]) : Adj b (algebraMap ℤ_[p] 𝕋 r) := by
  intro t s
  rw [algebraMap_smul, algebraMap_smul, πt_padicInt_smul, πt_padicInt_smul, map_zsmul, LinearMap.smul_apply,
    map_zsmul]

set_option maxHeartbeats 6400000 in
omit [NeZero M] in
theorem adj_add {τ τ' : 𝕋} (h : Adj b τ) (h' : Adj b τ') : Adj b (τ + τ') := by
  intro t s
  rw [add_smul, add_smul, πt_add, πt_add, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, h t s, h' t s]

omit [NeZero M] [Algebra ℤ_[p] 𝕋] [IsScalarTower ℤ_[p] 𝕋 (TateModule p (JH M H))] in
theorem adj_mul {τ τ' : 𝕋} (h : Adj b τ) (h' : Adj b τ') : Adj b (τ * τ') := by
  intro t s
  rw [mul_smul, h, h', ← mul_smul, mul_comm]

include hop hsa in
omit [NeZero M] in

theorem adj_of_adjoin_eq_top (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤) (τ : 𝕋) : Adj b τ := by
  have hτ : τ ∈ Algebra.adjoin ℤ_[p] (Set.range op) := by rw [hgen]; exact Algebra.mem_top
  induction hτ using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact adj_op b op hop hsa g
  | algebraMap r => exact adj_algebraMap b r
  | add x y _ _ hx hy => exact adj_add b hx hy
  | mul x y _ _ hx hy => exact adj_mul b hx hy

variable {e : 𝕋}

set_option maxHeartbeats 6400000 in
omit [NeZero M] in
theorem b_corner_anticorner (hadj : Adj b e) (he : IsIdempotentElem e) (t s : TateModule p (JH M H)) :
    b (πt (e • t)) (πt ((1 - e) • s)) = 0 := by
  have h1 : e • t = e • (e • t) := by rw [← mul_smul, he.eq]
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  rw [h1, hadj, ← mul_smul, h0, zero_smul 𝕋 s, πt_zero, LinearMap.map_zero (b _)]

set_option maxHeartbeats 6400000 in
omit [NeZero M] in
theorem b_anticorner_corner (hadj : Adj b e) (he : IsIdempotentElem e) (t s : TateModule p (JH M H)) :
    b (πt ((1 - e) • s)) (πt (e • t)) = 0 := by
  have h1 : e • t = e • (e • t) := by rw [← mul_smul, he.eq]
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  rw [h1, ← hadj, ← mul_smul, h0, zero_smul 𝕋 s, πt_zero, LinearMap.map_zero b, LinearMap.zero_apply]

omit [NeZero M] in

theorem mem_corner_map_iff (e : 𝕋) {z : JH M H} :
    z ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (JH M H)) e).toAddSubgroup).map
        (TateModule.proj p (JH M H) 1) ↔
      ∃ t : TateModule p (JH M H), TateModule.proj p (JH M H) 1 (e • t) = z := by
  constructor
  · intro hz
    rw [AddSubgroup.mem_map] at hz
    obtain ⟨y, hy, hyz⟩ := hz
    have hy' : y ∈ IharaLemma.cornerSubmodule (M := TateModule p (JH M H)) e := hy
    obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hy'
    refine ⟨t, ?_⟩
    rw [← hyz, ← ht]
    rfl
  · rintro ⟨t, ht⟩
    rw [AddSubgroup.mem_map]
    refine ⟨e • t, ?_, ht⟩
    show e • t ∈ IharaLemma.cornerSubmodule (M := TateModule p (JH M H)) e
    exact LinearMap.mem_range.mpr ⟨t, rfl⟩

omit [NeZero M] in
theorem decompose (e : 𝕋) (s : TateModule p (JH M H)) : πt s = πt (e • s) + πt ((1 - e) • s) := by
  rw [← πt_add, ← add_smul, add_sub_cancel, one_smul]

set_option maxHeartbeats 6400000 in
include hop hsa in

theorem main (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤) (e : 𝕋) (he : IsIdempotentElem e)
    (hbl : ∀ x : Jp M H p, (∀ y, b x y = 0) → x = 0) (hbr : ∀ y : Jp M H p, (∀ x, b x y = 0) → y = 0) :
    (∀ x : Jp M H p, (x : JH M H) ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (JH M H)) e).toAddSubgroup).map
          (TateModule.proj p (JH M H) 1) →
      (∀ y : Jp M H p, (y : JH M H) ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (JH M H)) e).toAddSubgroup).map
          (TateModule.proj p (JH M H) 1) → b x y = 0) → x = 0) ∧
    (∀ y : Jp M H p, (y : JH M H) ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (JH M H)) e).toAddSubgroup).map
          (TateModule.proj p (JH M H) 1) →
      (∀ x : Jp M H p, (x : JH M H) ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (JH M H)) e).toAddSubgroup).map
          (TateModule.proj p (JH M H) 1) → b x y = 0) → y = 0) := by
  have hadj : Adj b e := adj_of_adjoin_eq_top b op hop hsa hgen e
  constructor
  · intro x hx hX
    apply hbl x
    intro z
    obtain ⟨t, ht⟩ := (mem_corner_map_iff e).mp hx
    obtain ⟨s, hs⟩ := exists_πt_eq z
    have hxe : x = πt (e • t) := Subtype.ext ht.symm
    rw [← hs, decompose e s, LinearMap.BilinForm.add_right, hxe, b_corner_anticorner b hadj he, add_zero, ← hxe]
    exact hX _ ((mem_corner_map_iff e).mpr ⟨s, rfl⟩)
  · intro y hy hY
    apply hbr y
    intro z
    obtain ⟨t, ht⟩ := (mem_corner_map_iff e).mp hy
    obtain ⟨s, hs⟩ := exists_πt_eq z
    have hye : y = πt (e • t) := Subtype.ext ht.symm
    rw [← hs, decompose e s, LinearMap.BilinForm.add_left, hye, b_anticorner_corner b hadj he, add_zero, ← hye]
    exact hY _ ((mem_corner_map_iff e).mpr ⟨s, rfl⟩)

end Adjoint

end EOrth
p2m_reactivate "P2MW.S_ModularCurve_bilinForm_nondegenerate_on_map_proj_cornerSubmodule_tateModule_jH_of_selfAdjoint.EOrth"

end
p2m_reactivate "P2MW.S_ModularCurve_bilinForm_nondegenerate_on_map_proj_cornerSubmodule_tateModule_jH_of_selfAdjoint.EOrth"

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (ModularCurve.JH M H))]
    [IsScalarTower ℤ_[p] 𝕋 (TateModule p (ModularCurve.JH M H))]
    (op : CohCarrier.Gen M S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M S) (x : TateModule p (ModularCurve.JH M H)),
      op g • x = ModularCurve.tateGenOpH M H S p g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (e : 𝕋) (he : IsIdempotentElem e)
    (b : LinearMap.BilinForm (ZMod p) ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p))
    (hbl : ∀ x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), (∀ y, b x y = 0) → x = 0) (hbr : ∀ y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), (∀ x, b x y = 0) → y = 0)
    (hsa : ∀ (g : CohCarrier.Gen M S) (x y x' y' : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
      (x' : ModularCurve.JH M H) = ModularCurve.genOpH M H S g (x : ModularCurve.JH M H) →
      (y' : ModularCurve.JH M H) = ModularCurve.genOpH M H S g (y : ModularCurve.JH M H) → b x' y = b x y') :
    (∀ x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), (x : ModularCurve.JH M H) ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) e).toAddSubgroup).map (TateModule.proj p (ModularCurve.JH M H) 1) →
      (∀ y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), (y : ModularCurve.JH M H) ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) e).toAddSubgroup).map (TateModule.proj p (ModularCurve.JH M H) 1) → b x y = 0) → x = 0) ∧
    (∀ y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), (y : ModularCurve.JH M H) ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) e).toAddSubgroup).map (TateModule.proj p (ModularCurve.JH M H) 1) →
      (∀ x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), (x : ModularCurve.JH M H) ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) e).toAddSubgroup).map (TateModule.proj p (ModularCurve.JH M H) 1) → b x y = 0) → y = 0) :=
  EOrth.main b op hop hsa hgen e he hbl hbr

end S_ModularCurve_bilinForm_nondegenerate_on_map_proj_cornerSubmodule_tateModule_jH_of_selfAdjoint
end P2MW
export P2MW.S_ModularCurve_bilinForm_nondegenerate_on_map_proj_cornerSubmodule_tateModule_jH_of_selfAdjoint (solution)
