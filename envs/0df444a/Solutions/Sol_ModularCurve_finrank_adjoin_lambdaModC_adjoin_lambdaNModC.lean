-- Prove2me | solution 1 for ModularCurve.finrank_adjoin_lambdaModC_adjoin_lambdaNModC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/cc38d8f5-06b1-5c6a-a9d0-cdc4b0929e7d

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_LambdaSeries
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_relfinrank_full_eq_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_prime_pow
import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_adjoin_lambdaModC_eq_laurentBaseChange_modularFunctionFieldFull_four
import Theorems.Thm_ModularCurve_adjoin_lambdaModC_lambdaNModC_eq_laurentBaseChange_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_adjoin_lambdaModC_adjoin_lambdaNModC
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "ModularCurve~coeffEmb_qExpand P2MW.S_ModularCurve_finrank_adjoin_lambdaModC_adjoin_lambdaNModC.ModularCurve IntermediateField Polynomial"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_one_apply jq modularFunctionFieldFull jqd_mem_full coeffMap_coeff coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange lambdaModC lambdaNModC laurentMap_coeff relfinrank_laurentBaseChange_modularFunctionFieldFull relfinrank_full_eq_dedekindPsi dedekindPsi_prime_pow dedekindPsi_mul_of_coprime coeffMap_qExpand adjoin_lambdaModC_eq_laurentBaseChange_modularFunctionFieldFull_four adjoin_lambdaModC_lambdaNModC_eq_laurentBaseChange_modularFunctionFieldFull"
namespace FF4
p2m_open "ModularCurve~coeffEmb_qExpand"

variable (L : Type*) [Field L] [Algebra ℚ L]

theorem coeffEmb_lambdaModC : coeffEmb L (lambdaModC ℚ) = lambdaModC L := by
  ext k
  simp only [coeffEmb, coeffMap_coeff, lambdaModC, laurentMap_coeff]
  simp

abbrev K : IntermediateField L (LaurentSeries L) := IntermediateField.adjoin L ({lambdaModC L} : Set (LaurentSeries L))

abbrev J : IntermediateField L (LaurentSeries L) := IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L))

abbrev E : IntermediateField L (LaurentSeries L) := laurentBaseChange L (modularFunctionFieldFull 4)

theorem mu_mem_K : lambdaModC L ∈ K L := IntermediateField.mem_adjoin_simple_self L _

theorem coeffEmb_qExpand (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) := coeffMap_qExpand _ n x

theorem J_le_E : J L ≤ E L := by
  rw [J, IntermediateField.adjoin_simple_le_iff]
  have h := coeffEmb_mem_laurentBaseChange L (jqd_mem_full 4 (one_dvd 4))
  rwa [qExpand_one_apply] at h

theorem adjoin_lambdaModC_eq : IntermediateField.adjoin L ({lambdaModC L} : Set (LaurentSeries L))
      = laurentBaseChange L (modularFunctionFieldFull 4) :=
  ModularCurve.adjoin_lambdaModC_eq_laurentBaseChange_modularFunctionFieldFull_four L

theorem E_le_K : E L ≤ K L := (adjoin_lambdaModC_eq L).symm.le

theorem J_le_K : J L ≤ K L := (J_le_E L).trans (E_le_K L)

theorem finrank_EJ : Module.finrank (J L) (extendScalars (J_le_E L)) = 6 := by
  rw [← IntermediateField.relfinrank_eq_finrank_of_le (J_le_E L)]
  show IntermediateField.relfinrank (J L) (E L) = 6
  rw [J, E, relfinrank_laurentBaseChange_modularFunctionFieldFull, relfinrank_full_eq_dedekindPsi,
    show (4 : ℕ) = 2 ^ 2 by norm_num, dedekindPsi_prime_pow 2 2 Nat.prime_two two_ne_zero]
  norm_num

variable (q : ℕ) [Fact q.Prime]

abbrev K2 : IntermediateField L (LaurentSeries L) :=
  IntermediateField.adjoin L ({lambdaModC L, lambdaNModC L q} : Set (LaurentSeries L))

abbrev E2 : IntermediateField L (LaurentSeries L) := laurentBaseChange L (modularFunctionFieldFull (4 * q))

theorem K_le_K2 : K L ≤ K2 L q := IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

theorem adjoin_lambdaModC_lambdaNModC_eq :
    IntermediateField.adjoin L ({lambdaModC L, lambdaNModC L q} : Set (LaurentSeries L))
      = laurentBaseChange L (modularFunctionFieldFull (4 * q)) :=
  ModularCurve.adjoin_lambdaModC_lambdaNModC_eq_laurentBaseChange_modularFunctionFieldFull L q

theorem relfinrank_J_E2 (hq2 : q ≠ 2) : IntermediateField.relfinrank (J L) (E2 L q) = 6 * (q + 1) := by
  have hq : q.Prime := Fact.out
  have hcop : Nat.Coprime 4 q := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2))
  rw [J, E2, relfinrank_laurentBaseChange_modularFunctionFieldFull, relfinrank_full_eq_dedekindPsi,
    dedekindPsi_mul_of_coprime 4 q hcop, show (4 : ℕ) = 2 ^ 2 by norm_num,
    dedekindPsi_prime_pow 2 2 Nat.prime_two two_ne_zero]
  conv_lhs => rw [show q = q ^ 1 from (pow_one q).symm, dedekindPsi_prime_pow q 1 hq one_ne_zero]
  norm_num

theorem relfinrank_J_K : IntermediateField.relfinrank (J L) (K L) = 6 := by
  have hKE : K L = E L := adjoin_lambdaModC_eq L
  rw [IntermediateField.relfinrank_eq_finrank_of_le (J_le_K L)]
  have : extendScalars (J_le_K L) = extendScalars (J_le_E L) := by
    apply SetLike.coe_injective
    simp only [IntermediateField.coe_extendScalars]
    exact congrArg SetLike.coe hKE
  rw [this, finrank_EJ]

theorem relfinrank_K_K2 (hq2 : q ≠ 2) : IntermediateField.relfinrank (K L) (K2 L q) = q + 1 := by
  have htower := IntermediateField.relfinrank_mul_relfinrank (J_le_K L) (K_le_K2 L q)
  have h2 : IntermediateField.relfinrank (J L) (K2 L q) = 6 * (q + 1) := by
    have hKE : K2 L q = E2 L q := adjoin_lambdaModC_lambdaNModC_eq L q
    have := relfinrank_J_E2 L q hq2
    rwa [← hKE] at this
  rw [relfinrank_J_K, h2] at htower
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) htower

theorem extendScalars_K2_eq : extendScalars (K_le_K2 L q) =
    IntermediateField.adjoin (K L) ({lambdaNModC L q} : Set (LaurentSeries L)) := by
  apply le_antisymm
  · intro x hx
    rw [IntermediateField.mem_extendScalars] at hx
    have hle : K2 L q ≤ (IntermediateField.adjoin (K L) ({lambdaNModC L q} : Set (LaurentSeries L))).restrictScalars L := by
      rw [IntermediateField.adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨?_, IntermediateField.mem_adjoin_simple_self (K L) _⟩
      have h := (IntermediateField.adjoin (K L) ({lambdaNModC L q} : Set (LaurentSeries L))).algebraMap_mem
        ⟨lambdaModC L, mu_mem_K L⟩
      exact h
    exact (IntermediateField.mem_restrictScalars L).mp (hle hx)
  · rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_extendScalars]
    exact IntermediateField.subset_adjoin L _ (Set.mem_insert_of_mem _ rfl)

theorem finrank_K_adjoin (hq2 : q ≠ 2) :
    Module.finrank (K L) (IntermediateField.adjoin (K L) ({lambdaNModC L q} : Set (LaurentSeries L))) = q + 1 := by
  rw [← extendScalars_K2_eq, ← IntermediateField.relfinrank_eq_finrank_of_le (K_le_K2 L q), relfinrank_K_K2 L q hq2]

end ModularCurve.FF4

end

p2m_open "ModularCurve~coeffEmb_qExpand" in open _root_.P2MW.S_ModularCurve_finrank_adjoin_lambdaModC_adjoin_lambdaNModC.ModularCurve in
theorem solution (L : Type*) [Field L] [Algebra ℚ L] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) :
    Module.finrank (↥(IntermediateField.adjoin L ({lambdaModC L} : Set (LaurentSeries L))))
      (↥(IntermediateField.adjoin (↥(IntermediateField.adjoin L ({lambdaModC L} : Set (LaurentSeries L))))
        ({lambdaNModC L q} : Set (LaurentSeries L)))) = q + 1 :=
  ModularCurve.FF4.finrank_K_adjoin L q hq2

end S_ModularCurve_finrank_adjoin_lambdaModC_adjoin_lambdaNModC
end P2MW
export P2MW.S_ModularCurve_finrank_adjoin_lambdaModC_adjoin_lambdaNModC (solution)
