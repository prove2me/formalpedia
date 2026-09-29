-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_good_admissible_rep_heckeDivBar_self_good_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/02c88099-eaec-5dd4-98b2-ce5ddf0f29b3

import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_GlueData
import Theorems.Thm_ModularCurve_PlaceSpecialization_isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_good_admissible_rep_heckeDivBar_self_good_admissible
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe"

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

private theorem isNodeStable_nodePairsOfPlaces_of_forall_smul_mem
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (g : SemilinearAut K F) (W : Finset (Place K F)) (hW : ∀ w ∈ W, g • w ∈ W) :
    SemilinearAut.IsNodeStable (nodePairsOfPlaces g W) g := by
  intro s hs
  obtain ⟨w, hw, rfl⟩ := (mem_nodePairsOfPlaces_iff g W s).1 hs
  exact smulNodePair_mem_nodePairsOfPlaces g (hW w hw)

theorem solution
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (hαq : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) q)
      (hβq : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) q)
      [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar ((N * q) * q))],
        (∀ (x : JZero (N * q)),
          P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) x →
            ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                (F := ↥(modularFunctionFieldBar (N * q)))),
              P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∧
              P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) D
                ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ∧
              Pic0.mk D = x ∧
              P.IsGoodDiv (heckeDivBar hαq hβq
                (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) ∧
              P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (heckeDivBar hαq hβq
                    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
                ∈ GluingData.admissible
                    (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  intro W hW data hKr hα hβ P hαq hβq hPD x hx
  have hstab : SemilinearAut.IsNodeStable
      (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (arithFrobC q (ResidueField A) N) :=
    isNodeStable_nodePairsOfPlaces_of_forall_smul_mem _ W fun w hw =>
      (hW _).2 (arithFrobC_smul_mem_ssPlaces q N (ResidueField A) w ((hW w).1 hw))
  obtain ⟨D, hg, ha, hmk⟩ := hx
  have h := isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible N q hq hqN A hA W hW hstab
    data hKr hα hβ P hαq hβq
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) hg ha
  exact ⟨D, hg, ha, hmk, h.1, h.2.1⟩

end S_ModularCurve_PlaceSpecialization_exists_good_admissible_rep_heckeDivBar_self_good_admissible
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_good_admissible_rep_heckeDivBar_self_good_admissible (solution)
