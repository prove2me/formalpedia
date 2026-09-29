-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.degPts_zero_surjective_of_pushforwardAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/74889e2c-7d32-54f5-8454-819e66f635aa

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_ModularCurve_XHOperators
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_surjective
import Theorems.Thm_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_degPts_zero_surjective_of_pushforwardAlong
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (αH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) (hαint : αH.toRingHom.IsIntegral)
    (hαfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) αH)
    (_ : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))

    (hdeg0 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
        (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong αH hαint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        O.degPts 0 (Pic0.mk Dv) = Pic0.mk Dw) :
    Function.Surjective (O.degPts 0) := by
  classical

  have hsep : AlgebraicCurve.SeparableAlong (AlgebraicClosure ℚ) αH := by
    letI := AlgebraicCurve.algebraAlong αH
    haveI := AlgebraicCurve.isScalarTower_along αH
    haveI := AlgebraicCurve.isIntegral_along αH hαint
    haveI : Algebra.IsAlgebraic ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) := Algebra.IsIntegral.isAlgebraic
    show Algebra.IsSeparable _ _
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hsurj := AlgebraicCurve.Place.restrictAlong_surjective αH hαint hαfin hsep
  choose lift hlift using hsurj

  haveI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)
  have hinert : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), W.inertiaDegAlong αH hαint = 1 := fun W =>
    ModularCurve.inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC (CohCarrier.GammaH M H)
      (translation_mem_GammaH M H) (xHFunctionField M H) rfl αH hαint W

  have hsingle : ∀ (v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (n : ℤ),
      Divisor.pushforwardAlong αH hαint (Finsupp.single (lift v) n) = Finsupp.single v n := by
    intro v n
    have h1 : (lift v).restrictAlong αH hαint = v := hlift v
    have h2 : (lift v).inertiaDegAlong αH hαint = 1 := hinert (lift v)
    letI := AlgebraicCurve.algebraAlong αH
    haveI := AlgebraicCurve.isScalarTower_along αH
    haveI := AlgebraicCurve.isIntegral_along αH hαint
    show Divisor.pushforward _ (Finsupp.single (lift v) n) = _
    rw [Divisor.pushforward_single]
    change Finsupp.single ((lift v).restrictAlong αH hαint) (n * ((lift v).inertiaDegAlong αH hαint : ℤ)) = _
    rw [h1, h2, Nat.cast_one, mul_one]
  intro w
  obtain ⟨Dw, rfl⟩ := Pic0.mk_surjective w
  let Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    Finsupp.mapDomain lift (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
  have hpush : Divisor.pushforwardAlong αH hαint Dv = (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) := by
    show Divisor.pushforwardAlong αH hαint (Finsupp.mapDomain lift _) = _
    rw [Finsupp.mapDomain, map_finsuppSum]
    simp_rw [hsingle]
    exact Finsupp.sum_single _
  have hdeg : Dv ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) := by
    rw [Divisor.mem_degZero, ← Divisor.degree_pushforwardAlong αH hαint, hpush, ← Divisor.mem_degZero]
    exact Dw.2
  exact ⟨Pic0.mk ⟨Dv, hdeg⟩, hdeg0 ⟨Dv, hdeg⟩ Dw hpush.symm⟩

end S_ModularCurve_JHNeronObjectAtP_degPts_zero_surjective_of_pushforwardAlong
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_degPts_zero_surjective_of_pushforwardAlong (solution)
