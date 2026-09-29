-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/ed82afc6-fefd-5034-ae77-8204f4fb667e

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace_zero_and_ell_zero_eq_one_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p] :
    HasPrincipalDivisors κ (Fbar p M H hpM κ) ∧ ConstantsAreBase κ (Fbar p M H hpM κ) ∧
      ∀ v : Place κ (Fbar p M H hpM κ), Function.Surjective (algebraMap κ v.ResidueField) := by
  haveI : NeZero (M / p) := neZero_div p M hpM
  haveI : (ΓN p M H hpM).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH (M / p) _)

  obtain ⟨j, -, htr, hfd⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed κ (ΓN p M H hpM)
      (translation_mem_GammaH (M / p) _)
  haveI := hfd
  haveI hco : IsCurveOver κ (Fbar p M H hpM κ) := AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental j htr
  refine ⟨IsCurveOver.hasPrincipalDivisors, ?_, ?_⟩
  ·
    obtain ⟨hfin, hell⟩ :=
      AlgebraicCurve.finiteDimensional_lSpace_zero_and_ell_zero_eq_one_of_isAlgClosed_of_transcendental κ j htr hfd
    haveI := hfin
    show LSpace (0 : Divisor κ (Fbar p M H hpM κ)) = LinearMap.range (Algebra.linearMap κ (Fbar p M H hpM κ))
    refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
    · rintro _ ⟨c, rfl⟩
      exact algebraMap_mem_lSpace_zero c
    · rw [LinearMap.finrank_range_of_inj (f := Algebra.linearMap κ (Fbar p M H hpM κ)) (algebraMap κ (Fbar p M H hpM κ)).injective,
        Module.finrank_self]
      exact hell.symm
  ·
    intro v
    exact (Place.isRational_iff_deg_eq_one v).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed v)

end S_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar (solution)
