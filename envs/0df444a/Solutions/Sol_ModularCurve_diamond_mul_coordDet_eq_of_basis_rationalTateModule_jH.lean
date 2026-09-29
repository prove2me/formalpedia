-- Prove2me | solution 1 for ModularCurve.diamond_mul_coordDet_eq_of_basis_rationalTateModule_jH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/5495e4b3-3f15-5307-b553-cfb6713a3304

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ModularCurve_exists_diamondFrobeniusSimilitudePairing_rationalTateModule_jH
import Theorems.Thm_ModularCurve_heckeOperatorHAlong_comm
import Theorems.Thm_ModularCurve_heckeOperatorHAlong_diamondHBar_comm
import Theorems.Thm_ModularCurve_diamondHBar_mul
import Theorems.Thm_ModularCurve_galois_smul_genOpH_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_diamond_mul_coordDet_eq_of_basis_rationalTateModule_jH
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.decEqE ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk"
p2m_attr_erase "simp" "AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"

open scoped TensorProduct

set_option autoImplicit false

namespace WeilDetPkg

section Poly

open scoped IsMulCommutative

variable {K A' : Type} [Field K] [Ring A'] [Algebra K A'] (S : Subalgebra K A') [IsMulCommutative S]

theorem det_smul_identity (x c00 c01 c10 c11 : S) :
    c00 * (x * c11) - c01 * (x * c10) = x * (c00 * c11 - c10 * c01) := by
  ring

theorem sub_mul_right_comm (D d s : S) (ℓ : ℕ) :
    (D * d - ℓ) * s = D * s * d - ℓ * s := by
  ring

end Poly

variable {p : ℕ} [Fact p.Prime]
variable {T : Type} [AddCommGroup T] [Module ℤ_[p] T]

abbrev V (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[p] T] : Type :=
  ℚ_[p] ⊗[ℤ_[p]] T

noncomputable abbrev bc (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[p] T] :
    Module.End ℤ_[p] T →ₐ[ℤ_[p]] Module.End ℚ_[p] (V p T) :=
  Module.End.baseChangeHom ℤ_[p] ℚ_[p] T

theorem bc_apply (f : Module.End ℤ_[p] T) : bc p T f = f.baseChange ℚ_[p] := rfl

variable {ι₀ : Type} (A : ι₀ → Module.End ℤ_[p] T)

noncomputable def R (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[p] T]
    (A : ι₀ → Module.End ℤ_[p] T) : Subalgebra ℚ_[p] (Module.End ℚ_[p] (V p T)) :=
  Algebra.adjoin ℚ_[p] (Set.range fun g : ι₀ => (A g).baseChange ℚ_[p])

theorem bc_mem_R (i : ι₀) : bc p T (A i) ∈ R p T A :=
  Algebra.subset_adjoin ⟨i, rfl⟩

theorem isMulCommutative_R (hA : ∀ (g g' : ι₀) (x : T), A g (A g' x) = A g' (A g x)) :
    IsMulCommutative (R p T A) := by
  refine Algebra.isMulCommutative_adjoin ℚ_[p] ?_
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  show bc p T (A i) * bc p T (A j) = bc p T (A j) * bc p T (A i)
  rw [← map_mul, ← map_mul]
  congr 1
  exact LinearMap.ext fun x => hA i j x

theorem mul_comm_R [IsMulCommutative (R p T A)] (r s : R p T A) : r * s = s * r :=
  IsMulCommutative.is_comm.comm r s

variable (φ : Module.End ℤ_[p] T)

theorem commute_bc (hφ : ∀ (g : ι₀) (x : T), φ (A g x) = A g (φ x))
    {r : Module.End ℚ_[p] (V p T)} (hr : r ∈ R p T A) : r * bc p T φ = bc p T φ * r := by
  have hle : R p T A ≤ Subalgebra.centralizer ℚ_[p] {bc p T φ} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, rfl⟩ _ rfl
    show bc p T φ * bc p T (A i) = bc p T (A i) * bc p T φ
    rw [← map_mul, ← map_mul]
    congr 1
    exact LinearMap.ext fun x => hφ i x
  exact ((Subalgebra.mem_centralizer_iff ℚ_[p]).mp (hle hr) _ rfl).symm

variable (B : V p T →ₗ[ℚ_[p]] V p T →ₗ[ℚ_[p]] ℚ_[p])

theorem B_swap (halt : ∀ v, B v v = 0) (x y : V p T) : B x y = -B y x := by
  have h := halt (x + y)
  rw [LinearMap.map_add₂, map_add, map_add, halt x, halt y, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem bal_R [IsMulCommutative (R p T A)]
    (hbal : ∀ (g : ι₀) (x y : V p T), B (bc p T (A g) x) y = B x (bc p T (A g) y))
    {r : Module.End ℚ_[p] (V p T)} (hr : r ∈ R p T A) : ∀ x y : V p T, B (r x) y = B x (r y) := by
  induction hr using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨g, rfl⟩ := hf
    exact hbal g
  | algebraMap a =>
    intro x y
    rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, LinearMap.map_smul₂, map_smul]
  | add f g _ _ ihf ihg =>
    intro x y
    rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.map_add₂, map_add, ihf, ihg]
  | mul f g hf hg ihf ihg =>
    intro x y
    have hc : f * g = g * f := congrArg Subtype.val (mul_comm_R A (⟨f, hf⟩ : R p T A) ⟨g, hg⟩)
    conv_rhs => rw [hc]
    rw [Module.End.mul_apply, Module.End.mul_apply, ihf, ihg]

theorem B_self_R [IsMulCommutative (R p T A)] (halt : ∀ v, B v v = 0)
    (hbal : ∀ (g : ι₀) (x y : V p T), B (bc p T (A g) x) y = B x (bc p T (A g) y))
    {r : Module.End ℚ_[p] (V p T)} (hr : r ∈ R p T A) (x : V p T) : B x (r x) = 0 := by
  have h1 : B x (r x) = -B (r x) x := B_swap B halt x (r x)
  rw [bal_R A B hbal hr] at h1
  have h2 : B x (r x) + B x (r x) = 0 := add_eq_zero_iff_eq_neg.mpr h1
  rwa [add_self_eq_zero] at h2

variable (b : Module.Basis (Fin 2) (R p T A) (V p T))

noncomputable def lam (r : R p T A) : ℚ_[p] := B (b 0) ((r : Module.End ℚ_[p] (V p T)) (b 1))

theorem lam_neg (r : R p T A) : lam A B b (-r) = -lam A B b r := by
  simp only [lam, Subalgebra.coe_neg, LinearMap.neg_apply, map_neg]

theorem lam_sub (r s : R p T A) : lam A B b (r - s) = lam A B b r - lam A B b s := by
  simp only [lam, Subalgebra.coe_sub, LinearMap.sub_apply, map_sub]

theorem lam_natCast_mul (n : ℕ) (r : R p T A) : lam A B b (n * r) = (n : ℚ_[p]) * lam A B b r := by
  simp only [lam, Subalgebra.coe_mul, Module.End.mul_apply]
  have : ((n : R p T A) : Module.End ℚ_[p] (V p T)) = (n : Module.End ℚ_[p] (V p T)) :=
    map_natCast (R p T A).val n
  rw [this, Module.End.natCast_apply, map_nsmul, nsmul_eq_mul]

theorem expand (v : V p T) :
    v = (b.repr v 0 : Module.End ℚ_[p] (V p T)) (b 0) + (b.repr v 1 : Module.End ℚ_[p] (V p T)) (b 1) := by
  conv_lhs => rw [← b.sum_repr v]
  rw [Fin.sum_univ_two]
  rfl

section Comb

variable [IsMulCommutative (R p T A)]
  (halt : ∀ v, B v v = 0)
  (hbal : ∀ (g : ι₀) (x y : V p T), B (bc p T (A g) x) y = B x (bc p T (A g) y))

include hbal in
theorem B_coe_coe (r s : R p T A) (x y : V p T) :
    B ((r : Module.End ℚ_[p] (V p T)) x) ((s : Module.End ℚ_[p] (V p T)) y)
      = B x (((r * s : R p T A) : Module.End ℚ_[p] (V p T)) y) := by
  rw [bal_R A B hbal r.2, Subalgebra.coe_mul, Module.End.mul_apply]

include halt hbal in

theorem B_coe_same (r s : R p T A) (i : Fin 2) :
    B ((r : Module.End ℚ_[p] (V p T)) (b i)) ((s : Module.End ℚ_[p] (V p T)) (b i)) = 0 := by
  rw [B_coe_coe A B hbal]
  exact B_self_R A B halt hbal (r * s).2 (b i)

include hbal in

theorem B_coe_b0_b1 (r s : R p T A) :
    B ((r : Module.End ℚ_[p] (V p T)) (b 0)) ((s : Module.End ℚ_[p] (V p T)) (b 1))
      = lam A B b (r * s) := by
  rw [B_coe_coe A B hbal]; rfl

include halt hbal in

theorem B_coe_b1_b0 (r s : R p T A) :
    B ((r : Module.End ℚ_[p] (V p T)) (b 1)) ((s : Module.End ℚ_[p] (V p T)) (b 0))
      = -lam A B b (r * s) := by
  rw [B_coe_coe A B hbal, B_swap B halt, bal_R A B hbal (r * s).2]; rfl

include halt hbal in

theorem B_comb (r s t u : R p T A) :
    B ((r : Module.End ℚ_[p] (V p T)) (b 0) + (s : Module.End ℚ_[p] (V p T)) (b 1))
        ((t : Module.End ℚ_[p] (V p T)) (b 0) + (u : Module.End ℚ_[p] (V p T)) (b 1))
      = lam A B b (r * u - s * t) := by
  rw [LinearMap.map_add₂, map_add, map_add, B_coe_same A B b halt hbal, B_coe_b0_b1 A B b hbal,
    B_coe_b1_b0 A B b halt hbal, B_coe_same A B b halt hbal, zero_add, add_zero, ← sub_eq_add_neg,
    lam_sub]

end Comb

section Opaque

variable [IsMulCommutative (R p T A)]
variable (F : Module.End ℚ_[p] (V p T))
  (hF : ∀ r : R p T A, (r : Module.End ℚ_[p] (V p T)) * F = F * r)

noncomputable def detF : R p T A :=
  b.repr (F (b 0)) 0 * b.repr (F (b 1)) 1 - b.repr (F (b 1)) 0 * b.repr (F (b 0)) 1

omit [IsMulCommutative (R p T A)] in
include hF in
theorem F_coe_apply (r : R p T A) (v : V p T) :
    F ((r : Module.End ℚ_[p] (V p T)) v) = (r : Module.End ℚ_[p] (V p T)) (F v) := by
  rw [← Module.End.mul_apply, ← hF, Module.End.mul_apply]

variable (halt : ∀ v, B v v = 0) (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
  (hbal : ∀ (g : ι₀) (x y : V p T), B (bc p T (A g) x) y = B x (bc p T (A g) y))

include hF halt hbal in

theorem B_F_coe_b0_F_b1 (x : R p T A) :
    B (F ((x : Module.End ℚ_[p] (V p T)) (b 0))) (F (b 1)) = lam A B b (x * detF A b F) := by
  have h0 := expand A b (F (b 0))
  have h1 := expand A b (F (b 1))
  have e : (x : Module.End ℚ_[p] (V p T)) (F (b 1))
      = ((x * b.repr (F (b 1)) 0 : R p T A) : Module.End ℚ_[p] (V p T)) (b 0)
        + ((x * b.repr (F (b 1)) 1 : R p T A) : Module.End ℚ_[p] (V p T)) (b 1) := by
    conv_lhs => rw [h1]
    rw [map_add, Subalgebra.coe_mul, Subalgebra.coe_mul, Module.End.mul_apply, Module.End.mul_apply]
  rw [F_coe_apply A F hF, bal_R A B hbal x.2, e]
  conv_lhs => rw [h0]
  rw [B_comb A B b halt hbal, det_smul_identity (R p T A)]
  rfl

variable (Dr : R p T A) (ℓ : ℕ)
  (hsim : ∀ x y : V p T,
    B ((Dr : Module.End ℚ_[p] (V p T)) (F x)) (F y) = (ℓ : ℚ_[p]) * B x y)

noncomputable def rObs : R p T A := Dr * detF A b F - ℓ

include hF halt hbal hsim in

theorem lam_rObs_mul (s : R p T A) : lam A B b (rObs A b F Dr ℓ * s) = 0 := by
  have h := hsim ((s : Module.End ℚ_[p] (V p T)) (b 0)) (b 1)

  have hl : B ((Dr : Module.End ℚ_[p] (V p T)) (F ((s : Module.End ℚ_[p] (V p T)) (b 0)))) (F (b 1))
      = lam A B b (Dr * s * detF A b F) := by
    have e : (Dr : Module.End ℚ_[p] (V p T)) (F ((s : Module.End ℚ_[p] (V p T)) (b 0)))
        = F (((Dr * s : R p T A) : Module.End ℚ_[p] (V p T)) (b 0)) := by
      rw [← F_coe_apply A F hF, Subalgebra.coe_mul, Module.End.mul_apply]
    rw [e, B_F_coe_b0_F_b1 A B b F hF halt hbal]

  have hr' : (ℓ : ℚ_[p]) * B ((s : Module.End ℚ_[p] (V p T)) (b 0)) (b 1) = lam A B b (ℓ * s) := by
    rw [lam_natCast_mul, bal_R A B hbal s.2]; rfl
  rw [hl, hr'] at h
  have h2 : lam A B b (Dr * s * detF A b F - ℓ * s) = 0 := by rw [lam_sub, h, sub_self]
  rw [rObs, sub_mul_right_comm (R p T A) Dr (detF A b F) s ℓ, h2]

include hF halt hnd hbal hsim in

theorem rObs_b1 : (rObs A b F Dr ℓ : Module.End ℚ_[p] (V p T)) (b 1) = 0 := by
  refine hnd _ fun w => ?_
  have hw := expand A b w
  conv_lhs => rw [hw]
  rw [map_add, B_coe_b1_b0 A B b halt hbal, B_coe_same A B b halt hbal,
    lam_rObs_mul A B b F hF halt hbal Dr ℓ hsim, neg_zero, add_zero]

include hF halt hnd hbal hsim in

theorem rObs_b0 : (rObs A b F Dr ℓ : Module.End ℚ_[p] (V p T)) (b 0) = 0 := by
  refine hnd _ fun w => ?_
  have hw := expand A b w
  conv_lhs => rw [hw]
  rw [map_add, B_coe_same A B b halt hbal, B_coe_b0_b1 A B b hbal,
    lam_rObs_mul A B b F hF halt hbal Dr ℓ hsim, add_zero]

include hF halt hnd hbal hsim in

theorem coe_rObs : (rObs A b F Dr ℓ : Module.End ℚ_[p] (V p T)) = 0 := by
  refine LinearMap.ext fun v => ?_
  set r := rObs A b F Dr ℓ
  have hv := expand A b v
  have hc0 : (r : Module.End ℚ_[p] (V p T)) * (b.repr v 0 : Module.End ℚ_[p] (V p T))
      = (b.repr v 0 : Module.End ℚ_[p] (V p T)) * r :=
    congrArg Subtype.val (mul_comm_R A r (b.repr v 0))
  have hc1 : (r : Module.End ℚ_[p] (V p T)) * (b.repr v 1 : Module.End ℚ_[p] (V p T))
      = (b.repr v 1 : Module.End ℚ_[p] (V p T)) * r :=
    congrArg Subtype.val (mul_comm_R A r (b.repr v 1))
  rw [hv, map_add, ← Module.End.mul_apply, hc0, Module.End.mul_apply,
    rObs_b0 A B b F hF halt hnd hbal Dr ℓ hsim, map_zero, zero_add, ← Module.End.mul_apply, hc1,
    Module.End.mul_apply, rObs_b1 A B b F hF halt hnd hbal Dr ℓ hsim, map_zero,
    LinearMap.zero_apply]

include hF halt hnd hbal hsim in

theorem coe_mul_detF :
    (Dr : Module.End ℚ_[p] (V p T)) * (detF A b F : Module.End ℚ_[p] (V p T))
      = (ℓ : Module.End ℚ_[p] (V p T)) := by
  have h := coe_rObs A B b F hF halt hnd hbal Dr ℓ hsim
  rw [rObs, Subalgebra.coe_sub, Subalgebra.coe_mul, sub_eq_zero] at h
  rw [h]
  exact map_natCast (R p T A).val ℓ

end Opaque

theorem main [IsMulCommutative (R p T A)]
    (halt : ∀ v, B v v = 0) (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hbal : ∀ (g : ι₀) (x y : V p T), B (bc p T (A g) x) y = B x (bc p T (A g) y))
    (hφ : ∀ (g : ι₀) (x : T), φ (A g x) = A g (φ x))
    (g₀ : ι₀) (ℓ : ℕ)
    (hsim : ∀ x y : V p T,
      B (bc p T (A g₀) (bc p T φ x)) (bc p T φ y) = (ℓ : ℚ_[p]) * B x y) :
    (A g₀).baseChange ℚ_[p] *
        ((b.repr (φ.baseChange ℚ_[p] (b 0)) 0 * b.repr (φ.baseChange ℚ_[p] (b 1)) 1
            - b.repr (φ.baseChange ℚ_[p] (b 1)) 0 * b.repr (φ.baseChange ℚ_[p] (b 0)) 1 : R p T A) :
          Module.End ℚ_[p] (V p T))
      = (ℓ : Module.End ℚ_[p] (V p T)) := by
  have hDr : ((⟨bc p T (A g₀), bc_mem_R A g₀⟩ : R p T A) : Module.End ℚ_[p] (V p T))
      = (A g₀).baseChange ℚ_[p] := rfl
  rw [← hDr]
  exact coe_mul_detF A B b (bc p T φ) (fun r => commute_bc A φ hφ r.2) halt hnd hbal
    ⟨bc p T (A g₀), bc_mem_R A g₀⟩ ℓ hsim

end WeilDetPkg

namespace WeilDetJH

p2m_open "ModularCurve~baseChangeHom"

variable (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Finset ℕ)

omit [Fact p.Prime] in

theorem genOpH_comm (g g' : CohCarrier.Gen M (↑S : Set ℕ)) (P : JH M H) :
    genOpH M H (↑S : Set ℕ) g (genOpH M H (↑S : Set ℕ) g' P)
      = genOpH M H (↑S : Set ℕ) g' (genOpH M H (↑S : Set ℕ) g P) := by
  cases g with
  | T ℓ hℓ hℓS hℓM =>
    haveI := Fact.mk hℓ
    cases g' with
    | T ℓ' hℓ' hℓ'S hℓ'M =>
      haveI := Fact.mk hℓ'
      exact heckeOperatorHAlong_comm M H ℓ ℓ' P
    | U q hq hqM =>
      haveI := Fact.mk hq
      exact heckeOperatorHAlong_comm M H ℓ q P
    | dia d => exact heckeOperatorHAlong_diamondHBar_comm M H ℓ d P
  | U q hq hqM =>
    haveI := Fact.mk hq
    cases g' with
    | T ℓ' hℓ' hℓ'S hℓ'M =>
      haveI := Fact.mk hℓ'
      exact heckeOperatorHAlong_comm M H q ℓ' P
    | U q' hq' hq'M =>
      haveI := Fact.mk hq'
      exact heckeOperatorHAlong_comm M H q q' P
    | dia d => exact heckeOperatorHAlong_diamondHBar_comm M H q d P
  | dia d =>
    cases g' with
    | T ℓ' hℓ' hℓ'S hℓ'M =>
      haveI := Fact.mk hℓ'
      exact (heckeOperatorHAlong_diamondHBar_comm M H ℓ' d P).symm
    | U q' hq' hq'M =>
      haveI := Fact.mk hq'
      exact (heckeOperatorHAlong_diamondHBar_comm M H q' d P).symm
    | dia d' =>
      show diamondHBar M H d (diamondHBar M H d' P) = diamondHBar M H d' (diamondHBar M H d P)
      rw [← diamondHBar_mul, ← diamondHBar_mul, mul_comm]

theorem tateGenOpH_comm (g g' : CohCarrier.Gen M (↑S : Set ℕ)) (x : TateModule p (JH M H)) :
    tateGenOpH M H (↑S : Set ℕ) p g (tateGenOpH M H (↑S : Set ℕ) p g' x)
      = tateGenOpH M H (↑S : Set ℕ) p g' (tateGenOpH M H (↑S : Set ℕ) p g x) :=
  Subtype.ext (funext fun n => genOpH_comm M H S g g' ((x : ℕ → JH M H) n))

theorem galois_tateGenOpH_comm (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (g : CohCarrier.Gen M (↑S : Set ℕ)) (x : TateModule p (JH M H)) :
    JH.tateGaloisRep M H p σ (tateGenOpH M H (↑S : Set ℕ) p g x)
      = tateGenOpH M H (↑S : Set ℕ) p g (JH.tateGaloisRep M H p σ x) :=
  Subtype.ext (funext fun n => galois_smul_genOpH_comm M H (↑S : Set ℕ) σ g ((x : ℕ → JH M H) n))

end WeilDetJH

theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Finset ℕ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (b : Module.Basis (Fin 2)
      ↥(Algebra.adjoin ℚ_[p] (Set.range fun g : CohCarrier.Gen M (↑S : Set ℕ) =>
          (ModularCurve.tateGenOpH M H (↑S : Set ℕ) p g).baseChange ℚ_[p]))
      (TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H))))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M) (hℓp : ℓ ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) :
    (ModularCurve.tateGenOpH M H (↑S : Set ℕ) p (CohCarrier.Gen.dia
        (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))).baseChange ℚ_[p] *
      (↑((b.repr ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] (b 0))) 0 *
            (b.repr ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] (b 1))) 1 -
          (b.repr ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] (b 1))) 0 *
            (b.repr ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] (b 0))) 1) :
        Module.End ℚ_[p] (TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H)))) =
      (ℓ : Module.End ℚ_[p] (TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H)))) := by

  have _hS : ℓ ∉ (↑S : Set ℕ) := hℓS

  refine (ModularCurve.exists_diamondFrobeniusSimilitudePairing_rationalTateModule_jH M p H hin).elim
    fun B hB => ?_
  obtain ⟨hT, hD, halt, hnd, hsim⟩ := hB

  have hcommR : IsMulCommutative (WeilDetPkg.R p (TateModule p (ModularCurve.JH M H))
      (ModularCurve.tateGenOpH M H (↑S : Set ℕ) p)) :=
    WeilDetPkg.isMulCommutative_R _ (WeilDetJH.tateGenOpH_comm M p H S)

  have hbal : ∀ (g : CohCarrier.Gen M (↑S : Set ℕ))
      (x y : TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H))),
      B (WeilDetPkg.bc p _ (ModularCurve.tateGenOpH M H (↑S : Set ℕ) p g) x) y
        = B x (WeilDetPkg.bc p _ (ModularCurve.tateGenOpH M H (↑S : Set ℕ) p g) y) := by
    intro g x y
    cases g with
    | T ℓ' hℓ' hℓ'S hℓ'M => exact hT ℓ' hℓ' x y
    | U q hq hqM => exact hT q hq x y
    | dia d => exact hD d x y

  have hφ : ∀ (g : CohCarrier.Gen M (↑S : Set ℕ)) (x : TateModule p (ModularCurve.JH M H)),
      ModularCurve.JH.tateGaloisRep M H p σ (ModularCurve.tateGenOpH M H (↑S : Set ℕ) p g x)
        = ModularCurve.tateGenOpH M H (↑S : Set ℕ) p g (ModularCurve.JH.tateGaloisRep M H p σ x) :=
    fun g x => WeilDetJH.galois_tateGenOpH_comm M p H S σ g x

  have hsim' := hsim ℓ hℓ hℓM hℓp A hA σ hσ

  have hmain := @WeilDetPkg.main p _ (TateModule p (ModularCurve.JH M H)) _ _
    (CohCarrier.Gen M (↑S : Set ℕ)) (ModularCurve.tateGenOpH M H (↑S : Set ℕ) p)
    (ModularCurve.JH.tateGaloisRep M H p σ) B b hcommR halt hnd hbal hφ
    (CohCarrier.Gen.dia (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM))) ℓ hsim'
  exact hmain

end S_ModularCurve_diamond_mul_coordDet_eq_of_basis_rationalTateModule_jH
end P2MW
export P2MW.S_ModularCurve_diamond_mul_coordDet_eq_of_basis_rationalTateModule_jH (solution)
