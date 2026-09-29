-- Prove2me | solution 1 for ModularCurve.exists_unifFst_unifSnd_correctionDivisor_laws_of_ssPlaces
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/8632367d-5521-56cb-9c04-9269fce9991d

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces_univ
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_unifFst_unifSnd_correctionDivisor_laws_of_ssPlaces
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve ModularCurve

namespace LocUnif

theorem interp (k : Type*) [Field k] [IsAlgClosed k] (q N : ℕ) [CharP k q] [NeZero N] (hqN : ¬ q ∣ N) :
    ∀ (U Zv Za : Finset (Place k ↥(modularFunctionFieldC k N)))
    (t₀ : Place k ↥(modularFunctionFieldC k N)) (β : k)
    (val : Place k ↥(modularFunctionFieldC k N) → k) (bad : Finset k),
    Disjoint U Zv → Disjoint U Za → Disjoint Zv Za → t₀ ∉ U → t₀ ∉ Zv → t₀ ∉ Za →
    Zv.card + 2 * genusFF k ↥(modularFunctionFieldC k N) + 2 ≤ U.card →
    ∃ g : ↥(modularFunctionFieldC k N),
      g ∈ riemannRochSpace (∑ u ∈ U, Finsupp.single u (1 : ℤ)) ∧
      t₀.ord (g - algebraMap k ↥(modularFunctionFieldC k N) β) = 1 ∧
      (∀ z ∈ Zv, z.HasValue g (val z)) ∧
      (∀ z ∈ Za, ∃ γ : k, γ ∉ bad ∧ z.HasValue g γ) := by
  have h := ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC k q N hqN
  rw [h]
  intro U Zv Za t₀ β val bad h1 h2 h3 h4 h5 h6 h7
  exact ModularCurve.exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_modularFunctionFieldFullC k N U Zv Za t₀ β val bad
    h1 h2 h3 h4 h5 h6 h7

theorem exists_unif_corr (k : Type*) [Field k] [IsAlgClosed k] [DecidableEq k] (q N : ℕ) [Fact q.Prime] [CharP k q] [NeZero N]
    (hqN : ¬ q ∣ N)
    (W U : Finset (Place k ↥(modularFunctionFieldC k N))) (t : Place k ↥(modularFunctionFieldC k N)) (ht : t.IsRational)
    (hUW : Disjoint U W) (htU : t ∉ U) (hU : 2 * genusFF k ↥(modularFunctionFieldC k N) + 2 ≤ U.card) :
    ∃ (π : ↥(modularFunctionFieldC k N)) (R : Divisor k ↥(modularFunctionFieldC k N)),
      (∀ v, (Finsupp.single t (1 : ℤ) + R) v = v.ord π) ∧ (∀ v ∈ W, R v = 0) ∧ Divisor.degree R = -1 := by
  classical

  obtain ⟨g, hgL, hgt, -, hgW⟩ := interp k q N hqN U ∅ (W.erase t) t 0 (fun _ => 0) {0}
    (Finset.disjoint_empty_right _) (Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hUW)
    (Finset.disjoint_empty_left _) htU (Finset.notMem_empty _) (Finset.notMem_erase _ _)
    (by rw [Finset.card_empty, zero_add]; exact hU)
  rw [map_zero, sub_zero] at hgt
  have hg0 : g ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hgt; exact zero_ne_one hgt

  haveI : HasPrincipalDivisors k ↥(modularFunctionFieldC k N) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldC_of_perfectField k N
  obtain ⟨E, hE, hEdeg⟩ := HasPrincipalDivisors.exists_divisor (K := k) (F := ↥(modularFunctionFieldC k N)) g hg0
  refine ⟨g, E - Finsupp.single t 1, fun v => ?_, fun v hv => ?_, ?_⟩
  · rw [add_sub_cancel, hE]
  · rw [Finsupp.sub_apply, hE, Finsupp.single_apply]
    by_cases hvt : t = v
    · subst hvt; rw [if_pos rfl, hgt]; rfl
    · rw [if_neg hvt, sub_zero]
      obtain ⟨γ, hγ, hval⟩ := hgW v (Finset.mem_erase.mpr ⟨Ne.symm hvt, hv⟩)
      exact hval.ord_eq_zero (by simpa using hγ)
  · rw [map_sub, hEdeg, Divisor.degree_single, (Place.isRational_iff_deg_eq_one t).mp ht]
    norm_num

end LocUnif

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (N : ℕ) [NeZero N]
    (hqN : ¬ q ∣ N)
    (W : Finset (Place k ↥(modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (U : Finset (Place k ↥(modularFunctionFieldC k N))) (hUW : Disjoint U W)
    (hUφ : ∀ w ∈ W, arithFrobC q k N • w ∉ U)
    (hU : 2 * genusFF k ↥(modularFunctionFieldC k N) + 2 ≤ U.card) :
    ∃ (unifFst unifSnd : Place k ↥(modularFunctionFieldC k N) → ↥(modularFunctionFieldC k N))
      (corrFst corrSnd : Place k ↥(modularFunctionFieldC k N) → Divisor k ↥(modularFunctionFieldC k N)),
      ∀ w ∈ W,
        ((∀ v, (Finsupp.single w (1 : ℤ) + corrFst w) v = v.ord (unifFst w)) ∧ (∀ v ∈ W, corrFst w v = 0) ∧
          Divisor.degree (corrFst w) = -1) ∧
        ((∀ v, (Finsupp.single (arithFrobC q k N • w) (1 : ℤ) + corrSnd w) v = v.ord (unifSnd w)) ∧
          (∀ v ∈ W, corrSnd w v = 0) ∧ Divisor.degree (corrSnd w) = -1) := by
  classical
  have hrat : ∀ w ∈ W, w.IsRational := fun w hw => (hW w hw).1
  have hratφ : ∀ w ∈ W, (arithFrobC q k N • w).IsRational := fun w hw =>
    (ModularCurve.arithFrobC_smul_mem_ssPlaces_univ q N k _ (hW w hw)).1
  have hwU : ∀ w ∈ W, w ∉ U := fun w hw h => Finset.disjoint_left.mp hUW h hw
  have hF : ∀ w : Place k ↥(modularFunctionFieldC k N), w ∈ W →
      ∃ (π : ↥(modularFunctionFieldC k N)) (R : Divisor k ↥(modularFunctionFieldC k N)),
        (∀ v, (Finsupp.single w (1 : ℤ) + R) v = v.ord π) ∧ (∀ v ∈ W, R v = 0) ∧ Divisor.degree R = -1 :=
    fun w hw => LocUnif.exists_unif_corr k q N hqN W U w (hrat w hw) hUW (hwU w hw) hU
  have hS : ∀ w : Place k ↥(modularFunctionFieldC k N), w ∈ W →
      ∃ (π : ↥(modularFunctionFieldC k N)) (R : Divisor k ↥(modularFunctionFieldC k N)),
        (∀ v, (Finsupp.single (arithFrobC q k N • w) (1 : ℤ) + R) v = v.ord π) ∧ (∀ v ∈ W, R v = 0) ∧
          Divisor.degree R = -1 :=
    fun w hw => LocUnif.exists_unif_corr k q N hqN W U (arithFrobC q k N • w) (hratφ w hw) hUW (hUφ w hw) hU
  choose πF RF hF' using hF
  choose πS RS hS' using hS
  refine ⟨fun w => if h : w ∈ W then πF w h else 1, fun w => if h : w ∈ W then πS w h else 1,
    fun w => if h : w ∈ W then RF w h else 0, fun w => if h : w ∈ W then RS w h else 0, fun w hw => ?_⟩
  simp only [dif_pos hw]
  exact ⟨hF' w hw, hS' w hw⟩

end S_ModularCurve_exists_unifFst_unifSnd_correctionDivisor_laws_of_ssPlaces
end P2MW
export P2MW.S_ModularCurve_exists_unifFst_unifSnd_correctionDivisor_laws_of_ssPlaces (solution)
