-- Prove2me | solution 1 for ModularCurve.NodeLocalized.exists_mul_eq_mem_jIntegralClosure_of_not_isUnit_frobNodePair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/34ec9956-1c4e-56c1-b834-26c102bb7d7e

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_NodeDescent
import Theorems.Thm_ModularCurve_NodeLocalized_jqModC_mem_jIntegralClosure_and_jqNModC_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_exists_mul_eq_mem_jIntegralClosure_of_not_isUnit_frobNodePair
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar"
p2m_attr_erase "simp" "ModularCurve.coe_heckeAlphaBar"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized

noncomputable section

private theorem modularEval_mem_fieldOver {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (t : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval (1 * q) (coeffSubring A K) t ∈ fieldOver (1 * q) K := by
  induction t using MvPolynomial.induction_on with
  | C c =>
    simp only [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
    exact Subfield.subset_closure
      (Or.inl ⟨⟨(c : AlgebraicClosure ℚ), (Subring.mem_inf.mp c.2).2⟩, rfl⟩)
  | add p r hp hr =>
    rw [map_add]
    exact (fieldOver (1 * q) K).add_mem hp hr
  | mul_X p i hp =>
    rw [map_mul]
    refine (fieldOver (1 * q) K).mul_mem hp ?_
    simp only [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    exact Subfield.subset_closure (Or.inr (by fin_cases i <;> simp))

private theorem constSeries_mem_jIntegralClosure {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (c : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) c ∈ jIntegralClosure (1 * q) A K := by
  refine ⟨?_, ?_⟩
  · have h : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C c) =
        CharPReduction.constSeries (coeffSubring A K) c := MvPolynomial.eval₂Hom_C _ _ c
    rw [← h]
    exact modularEval_mem_fieldOver A K (MvPolynomial.C c)
  · have hmem : CharPReduction.constSeries (coeffSubring A K) c ∈ jRing A K :=
      Subring.subset_closure (Or.inl ⟨c, rfl⟩)
    exact isIntegral_algebraMap (x := (⟨_, hmem⟩ : ↥(jRing A K)))

private theorem modularEval_mem_jIntegralClosure {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (t : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval (1 * q) (coeffSubring A K) t ∈ jIntegralClosure (1 * q) A K := by
  induction t using MvPolynomial.induction_on with
  | C c =>
    have h : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C c) =
        CharPReduction.constSeries (coeffSubring A K) c := MvPolynomial.eval₂Hom_C _ _ c
    rw [h]
    exact constSeries_mem_jIntegralClosure A K c
  | add p r hp hr =>
    rw [map_add]
    exact add_mem hp hr
  | mul_X p i hp =>
    rw [map_mul]
    refine mul_mem hp ?_
    have h : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X i) =
        ![jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) (1 * q)] i := MvPolynomial.eval₂Hom_X' _ _ i
    rw [h]
    fin_cases i
    · exact (ModularCurve.NodeLocalized.jqModC_mem_jIntegralClosure_and_jqNModC_mem A K).1
    · exact (ModularCurve.NodeLocalized.jqModC_mem_jIntegralClosure_and_jqNModC_mem A K).2

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1)
    (h₁u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ∈ modularFunctionFieldC k 1)
    (h₂u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0)
    (hmem : (⟨_, h₁F⟩ : modularFunctionFieldC k 1) ∈ (frobNodePair q a).1.toValuationSubring)
    (hnu : ¬IsUnit (⟨_, hmem⟩ : (frobNodePair q a).1.toValuationSubring))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hfK : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K)
    (hfR : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈
      modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :
    ∃ (p s : ↥(jIntegralClosure (1 * q) A K))
      (s₀ : MvPolynomial (Fin 2) ↥(coeffSubring A K)),
      (s : LaurentSeries (AlgebraicClosure ℚ)) = modularEval (1 * q) (coeffSubring A K) s₀ ∧
      pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s₀ ≠ 0 ∧
      (f : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ)) =
        (p : LaurentSeries (AlgebraicClosure ℚ)) := by
  have _ := hker
  have _ := ha
  have _ := ha2
  have _ := h0
  have _ := h1728
  have _ := h₁
  have _ := h₁F
  have _ := h₁u
  have _ := h₂
  have _ := h₂F
  have _ := h₂u
  have _ := hmem
  have _ := hnu
  have _ := hfK
  obtain ⟨r, s₀, hs₀, hfs⟩ := hfR
  exact ⟨⟨_, modularEval_mem_jIntegralClosure A K r⟩, ⟨_, modularEval_mem_jIntegralClosure A K s₀⟩, s₀, rfl, hs₀, hfs⟩

end

#print axioms solution

end S_ModularCurve_NodeLocalized_exists_mul_eq_mem_jIntegralClosure_of_not_isUnit_frobNodePair
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_exists_mul_eq_mem_jIntegralClosure_of_not_isUnit_frobNodePair (solution)
