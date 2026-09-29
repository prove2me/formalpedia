-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.natCard_ssPlacesQExp_eq_toricRank_add_one_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/c5a3c7ac-36c0-569f-a250-f5fe55cddf6c

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_natCard_ssPlacesQExp_eq_natCard_ssPlacesQExp_of_isAlgClosed
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ValuationSubring_algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_natCard_ssPlacesQExp_eq_toricRank_add_one_univ
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open IsLocalRing

open ModularCurve AlgebraicCurve

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] :
    Nat.card ↥(ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) = O.toricRank + 1 := by
  classical

  have hκ : Nat.card ↥(ssPlacesQExp (ResidueField ↥A) (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p) =
      O.toricRank + 1 := by
    rw [O.toricRank_succ_eq_card, ← Nat.card_eq_finsetCard]
    symm
    apply Nat.card_congr
    refine
      { toFun := fun s => ⟨s.1.2, ?_⟩
        invFun := fun y => ⟨(qExpFrobeniusPlaceModL (ResidueField ↥A) (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p y.1, y.1), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have h := (O.mem_ssFinset_iff s.1).mp s.2
      rw [mem_ssNodePairsQExp_iff] at h
      exact h.1
    · rw [O.mem_ssFinset_iff]
      exact frob_mk_mem_ssNodePairsQExp y.2
    · intro s
      apply Subtype.ext
      have h := (O.mem_ssFinset_iff s.1).mp s.2
      rw [mem_ssNodePairsQExp_iff] at h
      exact Prod.ext h.2.symm rfl
    · intro y
      rfl

  rw [← hκ]
  haveI : (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)).FiniteIndex := inferInstance
  have hT := ModularCurve.translation_mem_GammaH (M / p) (infSubgroup p M H hpM)
  haveI := ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hT
  haveI := ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed (ResidueField ↥A)
    (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hT

  letI : Algebra (ZMod p) K := ZMod.algebra K p
  letI : Algebra (ZMod p) (ResidueField ↥A) := ZMod.algebra (ResidueField ↥A) p
  haveI : Algebra.IsAlgebraic (ZMod p) (ResidueField ↥A) :=
    ValuationSubring.algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat (AlgebraicClosure ℚ) A p
  letI : Algebra (ResidueField ↥A) K := (IsAlgClosed.lift : ResidueField ↥A →ₐ[ZMod p] K).toRingHom.toAlgebra
  obtain ⟨xK, -, hxK, hfK⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K
    (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hT
  obtain ⟨xκ, -, hxκ, hfκ⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed (ResidueField ↥A)
    (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hT
  exact ModularCurve.natCard_ssPlacesQExp_eq_natCard_ssPlacesQExp_of_isAlgClosed p (ResidueField ↥A) K
    (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) ⟨xκ, hxκ, hfκ⟩ ⟨xK, hxK, hfK⟩

end S_ModularCurve_JHNeronObjectAtP_natCard_ssPlacesQExp_eq_toricRank_add_one_univ
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_natCard_ssPlacesQExp_eq_toricRank_add_one_univ (solution)
