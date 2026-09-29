-- Prove2me | solution 1 for ModularCurve.inv_smul_D_eq_zero_iff_mk_eq_zero_of_coe_eq_coeffMap_of_forall_mul_eq_ord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/c637dca5-0d57-5a10-bbed-4e30ca9480b1

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_HeckeDifferential
import Theorems.Thm_AlgebraicCurve_inv_smul_D_eq_zero_iff_exists_pow_eq
import Theorems.Thm_AlgebraicCurve_Pic0_mk_eq_zero_iff_exists_pow
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_ModularCurve_diffQExp_qExpFunctionFieldC_injective
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_essFiniteType_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_inv_smul_D_eq_zero_iff_mk_eq_zero_of_coe_eq_coeffMap_of_forall_mul_eq_ord
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

theorem T4aP2B.qEuler_coeffMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : LaurentSeries R) :
    ModularCurve.qEuler S (ModularCurve.coeffMap f x) = ModularCurve.coeffMap f (ModularCurve.qEuler R x) := by
  ext n
  simp [ModularCurve.qEuler_coeff, ModularCurve.coeffMap_coeff]

theorem T4aP2B.coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (ModularCurve.coeffMap f) := by
  intro a b h
  ext n
  apply hf
  have := congrArg (fun s : LaurentSeries S => s.coeff n) h
  simpa [ModularCurve.coeffMap_coeff] using this

theorem T4aP2B.inv_smul_D_eq_zero_iff_D_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F) (hx : x ≠ 0) :
    x⁻¹ • KaehlerDifferential.D K F x = 0 ↔ KaehlerDifferential.D K F x = 0 := by
  rw [smul_eq_zero, or_iff_right (inv_ne_zero hx)]

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p]
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra κ K]
    (eK : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ →+* ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
    (heK : ∀ g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ, ((eK g : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = ModularCurve.coeffMap (algebraMap κ K) (g : LaurentSeries κ))
    (plK : AlgebraicCurve.Place κ (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ) → AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))))
    (hplK : ∀ (g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ) (v : AlgebraicCurve.Place κ (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ)), (plK v).ord (eK g) = v.ord g)
    (g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ) (hg : g ≠ 0)
    (E : AlgebraicCurve.Divisor.degZero (K := κ) (F := ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ))
    (hE : ∀ v : AlgebraicCurve.Place κ (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ), (p : ℤ) * (E : AlgebraicCurve.Divisor κ (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ)) v = v.ord g) :
    (eK g)⁻¹ • KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (eK g) = 0 ↔ AlgebraicCurve.Pic0.mk E = 0 := by
  classical

  have hT : ModularGroup.T ∈ (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) := ModularCurve.translation_mem_GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)
  haveI instNZ : NeZero (M / p) := ModularCurve.neZero_div p M hpM
  haveI instFI : (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)).FiniteIndex := inferInstance
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap κ K).injective p
  haveI : Algebra.EssFiniteType κ (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ) := ModularCurve.essFiniteType_qExpFunctionFieldC_of_isAlgClosed κ _ hT
  haveI : AlgebraicCurve.IsCurveOver κ (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ) := ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed κ _ hT
  haveI : Algebra.EssFiniteType K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) := ModularCurve.essFiniteType_qExpFunctionFieldC_of_isAlgClosed K _ hT
  haveI : AlgebraicCurve.IsCurveOver K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) := ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed K _ hT
  have hg' : eK g ≠ 0 := (map_ne_zero_iff eK eK.injective).mpr hg

  have hinjK := ModularCurve.diffQExp_qExpFunctionFieldC_injective K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) hT
  have hinjκ := ModularCurve.diffQExp_qExpFunctionFieldC_injective κ (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) hT
  have h12 : (eK g)⁻¹ • KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (eK g) = 0 ↔
      ModularCurve.qEuler K ((eK g : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = 0 := by
    rw [T4aP2B.inv_smul_D_eq_zero_iff_D_eq_zero _ hg', ← map_eq_zero_iff _ hinjK, ModularCurve.diffQExp_D]

  have h3 : ModularCurve.qEuler K ((eK g : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = 0 ↔ ModularCurve.qEuler κ ((g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ) : LaurentSeries κ) = 0 := by
    rw [heK, T4aP2B.qEuler_coeffMap, map_eq_zero_iff _ (T4aP2B.coeffMap_injective _ (algebraMap κ K).injective)]

  have h4 : ModularCurve.qEuler κ ((g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ) : LaurentSeries κ) = 0 ↔ ∃ h : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ, h ^ p = g := by
    rw [← ModularCurve.diffQExp_D, map_eq_zero_iff _ hinjκ, ← T4aP2B.inv_smul_D_eq_zero_iff_D_eq_zero _ hg]
    exact AlgebraicCurve.inv_smul_D_eq_zero_iff_exists_pow_eq p g hg

  obtain ⟨j, -, hjtr, hjfd⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed κ (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) hT
  haveI := hjfd
  have hconst : ∀ u : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ, u ≠ 0 → (∀ v : AlgebraicCurve.Place κ (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ), v.ord u = 0) → u ∈ (algebraMap κ (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ)).range :=
    fun u _ hu => AlgebraicCurve.Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed j hjtr hu
  have h5 : AlgebraicCurve.Pic0.mk E = 0 ↔ ∃ h : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ, h ≠ 0 ∧ g = h ^ p :=
    AlgebraicCurve.Pic0.mk_eq_zero_iff_exists_pow hconst (Fact.out : p.Prime).ne_zero hg (fun v => (hE v).symm)
  rw [h12, h3, h4, h5]
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨h, ?_, rfl⟩
    rintro rfl
    exact hg (by simp [(Fact.out : p.Prime).ne_zero])
  · rintro ⟨h, -, rfl⟩
    exact ⟨h, rfl⟩

end S_ModularCurve_inv_smul_D_eq_zero_iff_mk_eq_zero_of_coe_eq_coeffMap_of_forall_mul_eq_ord
end P2MW
export P2MW.S_ModularCurve_inv_smul_D_eq_zero_iff_mk_eq_zero_of_coe_eq_coeffMap_of_forall_mul_eq_ord (solution)
