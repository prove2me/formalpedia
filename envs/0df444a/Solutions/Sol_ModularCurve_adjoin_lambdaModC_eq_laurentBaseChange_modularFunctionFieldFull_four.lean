-- Prove2me | solution 1 for ModularCurve.adjoin_lambdaModC_eq_laurentBaseChange_modularFunctionFieldFull_four
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/e899ee53-2b89-5153-a52f-268c56455561

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_LambdaSeries
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_relfinrank_full_eq_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_prime_pow
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_transcendental_lambdaModC
import Theorems.Thm_ModularCurve_qExpand_two_jq_mul_lambdaModC_sq
import Theorems.Thm_ModularCurve_jq_mul_lambdaModC_mul_one_sub_pow_four
import Theorems.Thm_ModularCurve_qExpand_four_jq_mul_one_sub_mul_lambdaModC_pow_four
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_adjoin_lambdaModC_eq_laurentBaseChange_modularFunctionFieldFull_four
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "ModularCurve~coeffEmb_qExpand P2MW.S_ModularCurve_adjoin_lambdaModC_eq_laurentBaseChange_modularFunctionFieldFull_four.ModularCurve IntermediateField Polynomial"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_one_apply jq modularFunctionFieldFull jqd_mem_full coeffMap_coeff coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange lambdaModC laurentMap_coeff laurentBaseChange_adjoin relfinrank_laurentBaseChange_modularFunctionFieldFull relfinrank_full_eq_dedekindPsi dedekindPsi_prime_pow coeffMap_qExpand transcendental_lambdaModC qExpand_two_jq_mul_lambdaModC_sq jq_mul_lambdaModC_mul_one_sub_pow_four qExpand_four_jq_mul_one_sub_mul_lambdaModC_pow_four"
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

theorem charZero_L : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective

theorem mu_mem_K : lambdaModC L ∈ K L := IntermediateField.mem_adjoin_simple_self L _

theorem aeval_mu_ne_zero {p : L[X]} (hp : p ≠ 0) : aeval (lambdaModC L) p ≠ 0 := by
  intro h
  exact (transcendental_lambdaModC L) ⟨p, hp, h⟩

theorem mem_of_mul_eq {F : IntermediateField L (LaurentSeries L)} {x d c : LaurentSeries L}
    (h : x * d = c) (hd : d ∈ F) (hc : c ∈ F) (hd0 : d ≠ 0) : x ∈ F := by
  have : x = c * d⁻¹ := by rw [← h, mul_inv_cancel_right₀ hd0]
  rw [this]
  exact mul_mem hc (inv_mem hd)

theorem coeffEmb_qExpand (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) := coeffMap_qExpand _ n x

theorem J_le_E : J L ≤ E L := by
  rw [J, IntermediateField.adjoin_simple_le_iff]
  have h := coeffEmb_mem_laurentBaseChange L (jqd_mem_full 4 (one_dvd 4))
  rwa [qExpand_one_apply] at h

theorem JM_L : coeffEmb L jq * lambdaModC L * (1 - 16 * lambdaModC L) ^ 4 =
    (1 + 224 * lambdaModC L + 256 * lambdaModC L ^ 2) ^ 3 := by
  have h := congrArg (coeffEmb L) jq_mul_lambdaModC_mul_one_sub_pow_four
  simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, coeffEmb_lambdaModC] at h
  exact h

theorem JL_L : qExpand L 2 (coeffEmb L jq) * lambdaModC L ^ 2 * (16 * lambdaModC L - 1) ^ 2 =
    (256 * lambdaModC L ^ 2 - 16 * lambdaModC L + 1) ^ 3 := by
  have h := congrArg (coeffEmb L) qExpand_two_jq_mul_lambdaModC_sq
  simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, coeffEmb_lambdaModC] at h
  rwa [coeffEmb, coeffMap_qExpand] at h

theorem J4M_L : qExpand L 4 (coeffEmb L jq) * (1 - 16 * lambdaModC L) * lambdaModC L ^ 4 =
    (1 - 16 * lambdaModC L + 16 * lambdaModC L ^ 2) ^ 3 := by
  have h := congrArg (coeffEmb L) qExpand_four_jq_mul_one_sub_mul_lambdaModC_pow_four
  simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, coeffEmb_lambdaModC] at h
  rwa [coeffEmb, coeffMap_qExpand] at h

theorem j_mem_K : coeffEmb L jq ∈ K L := by
  have hμ := mu_mem_K L
  refine mem_of_mul_eq L (d := lambdaModC L * (1 - 16 * lambdaModC L) ^ 4)
    (c := (1 + 224 * lambdaModC L + 256 * lambdaModC L ^ 2) ^ 3) ?_ ?_ ?_ ?_
  · rw [← JM_L L]; ring
  · exact mul_mem hμ (pow_mem (sub_mem (one_mem _) (mul_mem (by exact_mod_cast IntermediateField.natCast_mem (K L) 16) hμ)) _)
  · exact pow_mem (add_mem (add_mem (one_mem _) (mul_mem (by exact_mod_cast IntermediateField.natCast_mem (K L) 224) hμ))
      (mul_mem (by exact_mod_cast IntermediateField.natCast_mem (K L) 256) (pow_mem hμ _))) _
  · have : lambdaModC L * (1 - 16 * lambdaModC L) ^ 4 = aeval (lambdaModC L) (X * (1 - C (16:L) * X) ^ 4 : L[X]) := by
      simp [map_ofNat]
    rw [this]
    apply aeval_mu_ne_zero
    refine mul_ne_zero X_ne_zero (pow_ne_zero _ ?_)
    intro h
    have := congrArg (fun p : L[X] => p.coeff 0) h
    simp at this

theorem j2_mem_K : qExpand L 2 (coeffEmb L jq) ∈ K L := by
  have hμ := mu_mem_K L
  refine mem_of_mul_eq L (d := lambdaModC L ^ 2 * (16 * lambdaModC L - 1) ^ 2)
    (c := (256 * lambdaModC L ^ 2 - 16 * lambdaModC L + 1) ^ 3) ?_ ?_ ?_ ?_
  · rw [← JL_L L]; ring
  · exact mul_mem (pow_mem hμ _) (pow_mem (sub_mem (mul_mem (by exact_mod_cast IntermediateField.natCast_mem (K L) 16) hμ) (one_mem _)) _)
  · exact pow_mem (add_mem (sub_mem (mul_mem (by exact_mod_cast IntermediateField.natCast_mem (K L) 256) (pow_mem hμ _))
      (mul_mem (by exact_mod_cast IntermediateField.natCast_mem (K L) 16) hμ)) (one_mem _)) _
  · have : lambdaModC L ^ 2 * (16 * lambdaModC L - 1) ^ 2 = aeval (lambdaModC L) (X ^ 2 * (C (16:L) * X - 1) ^ 2 : L[X]) := by
      simp [map_ofNat]
    rw [this]
    apply aeval_mu_ne_zero
    refine mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ ?_)
    intro h
    have := congrArg (fun p : L[X] => p.coeff 0) h
    simp at this

theorem j4_mem_K : qExpand L 4 (coeffEmb L jq) ∈ K L := by
  have hμ := mu_mem_K L
  refine mem_of_mul_eq L (d := (1 - 16 * lambdaModC L) * lambdaModC L ^ 4)
    (c := (1 - 16 * lambdaModC L + 16 * lambdaModC L ^ 2) ^ 3) ?_ ?_ ?_ ?_
  · rw [← J4M_L L]; ring
  · exact mul_mem (sub_mem (one_mem _) (mul_mem (by exact_mod_cast IntermediateField.natCast_mem (K L) 16) hμ)) (pow_mem hμ _)
  · exact pow_mem (add_mem (sub_mem (one_mem _) (mul_mem (by exact_mod_cast IntermediateField.natCast_mem (K L) 16) hμ))
      (mul_mem (by exact_mod_cast IntermediateField.natCast_mem (K L) 16) (pow_mem hμ _))) _
  · have : (1 - 16 * lambdaModC L) * lambdaModC L ^ 4 = aeval (lambdaModC L) ((1 - C (16:L) * X) * X ^ 4 : L[X]) := by
      simp [map_ofNat]
    rw [this]
    apply aeval_mu_ne_zero
    refine mul_ne_zero ?_ (pow_ne_zero _ X_ne_zero)
    intro h
    have := congrArg (fun p : L[X] => p.coeff 0) h
    simp at this

theorem E_le_K : E L ≤ K L := by
  rw [E, modularFunctionFieldFull, laurentBaseChange_adjoin, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, ⟨d, hd, hdvd, rfl⟩, rfl⟩
  have hd0 : d ≠ 0 := hd.out
  have hle : d ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases d
  · exact absurd rfl hd0
  · rw [qExpand_one_apply]; exact j_mem_K L
  · rw [SetLike.mem_coe, coeffEmb_qExpand]; exact j2_mem_K L
  · exact absurd hdvd (by norm_num)
  · rw [SetLike.mem_coe, coeffEmb_qExpand]; exact j4_mem_K L

theorem J_le_K : J L ≤ K L := (J_le_E L).trans (E_le_K L)

theorem finrank_EJ : Module.finrank (J L) (extendScalars (J_le_E L)) = 6 := by
  rw [← IntermediateField.relfinrank_eq_finrank_of_le (J_le_E L)]
  show IntermediateField.relfinrank (J L) (E L) = 6
  rw [J, E, relfinrank_laurentBaseChange_modularFunctionFieldFull, relfinrank_full_eq_dedekindPsi,
    show (4 : ℕ) = 2 ^ 2 by norm_num, dedekindPsi_prime_pow 2 2 Nat.prime_two two_ne_zero]
  norm_num

def jJ : J L := ⟨coeffEmb L jq, IntermediateField.mem_adjoin_simple_self L _⟩

def P6 : (J L)[X] := (1 + C (224 : J L) * X + C (256 : J L) * X ^ 2) ^ 3 - C (jJ L) * (X * (1 - C (16 : J L) * X) ^ 4)

theorem natDegree_P6 : (P6 L).natDegree = 6 := by
  haveI := charZero_L L
  unfold P6
  compute_degree!

theorem P6_ne_zero : P6 L ≠ 0 := by
  intro h; have := natDegree_P6 L; rw [h, natDegree_zero] at this; exact absurd this (by norm_num)

theorem aeval_P6 : aeval (lambdaModC L) (P6 L) = 0 := by
  have h := JM_L L
  have hj : algebraMap (J L) (LaurentSeries L) (jJ L) = coeffEmb L jq := rfl
  simp only [P6, map_sub, map_mul, map_pow, map_add, map_one, aeval_C, aeval_X, hj, map_ofNat]
  rw [← h]; ring

theorem isIntegral_mu : IsIntegral (J L) (lambdaModC L) := by
  have halg : IsAlgebraic (J L) (lambdaModC L) := ⟨P6 L, P6_ne_zero L, aeval_P6 L⟩
  exact halg.isIntegral

theorem extendScalars_K_eq : extendScalars (J_le_K L) =
    IntermediateField.adjoin (J L) ({lambdaModC L} : Set (LaurentSeries L)) := by
  apply le_antisymm
  · intro x hx
    rw [IntermediateField.mem_extendScalars] at hx
    have hle : K L ≤ (IntermediateField.adjoin (J L) ({lambdaModC L} : Set (LaurentSeries L))).restrictScalars L :=
      IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (IntermediateField.mem_adjoin_simple_self (J L) _))
    exact (IntermediateField.mem_restrictScalars L).mp (hle hx)
  · rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_extendScalars]
    exact mu_mem_K L

theorem finrank_KJ_le : Module.finrank (J L) (extendScalars (J_le_K L)) ≤ 6 := by
  rw [extendScalars_K_eq, IntermediateField.adjoin.finrank (isIntegral_mu L), ← natDegree_P6 L]
  exact Polynomial.natDegree_le_of_dvd (minpoly.dvd (J L) _ (aeval_P6 L)) (P6_ne_zero L)

scoped instance : FiniteDimensional (J L) (extendScalars (J_le_K L)) := by
  rw [extendScalars_K_eq]
  exact IntermediateField.adjoin.finiteDimensional (isIntegral_mu L)

theorem adjoin_lambdaModC_eq : IntermediateField.adjoin L ({lambdaModC L} : Set (LaurentSeries L))
      = laurentBaseChange L (modularFunctionFieldFull 4) := by
  have hle : extendScalars (J_le_E L) ≤ extendScalars (J_le_K L) :=
    (IntermediateField.extendScalars_le_extendScalars_iff _ _).mpr (E_le_K L)
  have heq := IntermediateField.eq_of_le_of_finrank_le hle (by rw [finrank_EJ]; exact finrank_KJ_le L)
  have hcoe := congrArg (fun M : IntermediateField (J L) (LaurentSeries L) => (M : Set (LaurentSeries L))) heq
  simp only [IntermediateField.coe_extendScalars] at hcoe
  exact (SetLike.coe_injective hcoe).symm

end ModularCurve.FF4
p2m_reactivate "P2MW.S_ModularCurve_adjoin_lambdaModC_eq_laurentBaseChange_modularFunctionFieldFull_four.ModularCurve P2MW.S_ModularCurve_adjoin_lambdaModC_eq_laurentBaseChange_modularFunctionFieldFull_four.ModularCurve.FF4"
p2m_reactivate "P2MW.S_ModularCurve_adjoin_lambdaModC_eq_laurentBaseChange_modularFunctionFieldFull_four.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_adjoin_lambdaModC_eq_laurentBaseChange_modularFunctionFieldFull_four.ModularCurve P2MW.S_ModularCurve_adjoin_lambdaModC_eq_laurentBaseChange_modularFunctionFieldFull_four.ModularCurve.FF4"

p2m_open "ModularCurve~coeffEmb_qExpand" in open _root_.P2MW.S_ModularCurve_adjoin_lambdaModC_eq_laurentBaseChange_modularFunctionFieldFull_four.ModularCurve in
theorem solution (L : Type*) [Field L] [Algebra ℚ L] :
    IntermediateField.adjoin L ({lambdaModC L} : Set (LaurentSeries L))
      = laurentBaseChange L (modularFunctionFieldFull 4) :=
  ModularCurve.FF4.adjoin_lambdaModC_eq L

end S_ModularCurve_adjoin_lambdaModC_eq_laurentBaseChange_modularFunctionFieldFull_four
end P2MW
export P2MW.S_ModularCurve_adjoin_lambdaModC_eq_laurentBaseChange_modularFunctionFieldFull_four (solution)
