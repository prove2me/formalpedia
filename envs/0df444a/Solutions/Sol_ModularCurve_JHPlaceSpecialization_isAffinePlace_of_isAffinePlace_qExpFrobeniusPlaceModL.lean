-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.isAffinePlace_of_isAffinePlace_qExpFrobeniusPlaceModL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/b5990b63-d3c9-5335-be57-e28c3439ae01

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_isAffinePlace_of_isAffinePlace_qExpFrobeniusPlaceModL
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

namespace ConvHaff

theorem surjK {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

theorem mem_of_pow_mem {F : Type*} [Field F] (O : ValuationSubring F) {x : F} {n : ℕ} (hn : n ≠ 0) (h : x ^ n ∈ O) : x ∈ O := by
  rw [← O.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff hn).mp h

end ConvHaff

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] :
    ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      JHPlaceSpecialization.IsAffinePlace p M H hpM A (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v) →
      JHPlaceSpecialization.IsAffinePlace p M H hpM A v := by
  classical
  haveI : (JHNeronObjectAtP.ΓN p M H hpM).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM))
  have hT : ModularGroup.T ∈ JHNeronObjectAtP.ΓN p M H hpM := ModularCurve.translation_mem_GammaH (M / p) (infSubgroup p M H hpM)
  haveI : IsCurveOver (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :=
    ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) hT
  rintro v ⟨x, a, hxj, hval⟩

  have hfix : ∀ k : ℤ, ((x : LaurentSeries (ResidueField ↥A)).coeff k) ^ p = (x : LaurentSeries (ResidueField ↥A)).coeff k := by
    intro k
    rw [hxj, jqModC_eq_map_intCast, HahnSeries.map_coeff]
    exact intCast_pow_char_eq (ResidueField ↥A) p _
  have hFx : qExpFrobeniusModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p x = x ^ p := by
    apply Subtype.ext
    rw [coe_qExpFrobeniusModL, SubmonoidClass.coe_pow]
    exact qExpand_eq_pow_of_coeff_fixed (ResidueField ↥A) p _ hfix

  have hmemp : x ^ p ∈ v.toValuationSubring := by
    rw [← hFx, ← mem_qExpFrobeniusPlaceModL_iff]
    exact hval.mem
  have hmem : x ∈ v.toValuationSubring := ConvHaff.mem_of_pow_mem _ (Fact.out : p.Prime).ne_zero hmemp
  obtain ⟨b, hb, -⟩ := v.exists_hasValue_of_surjective (ConvHaff.surjK _) hmem
  exact ⟨x, b, hxj, hb⟩

end S_ModularCurve_JHPlaceSpecialization_isAffinePlace_of_isAffinePlace_qExpFrobeniusPlaceModL
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_isAffinePlace_of_isAffinePlace_qExpFrobeniusPlaceModL (solution)
