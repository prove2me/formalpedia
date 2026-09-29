-- Prove2me | solution 1 for ModularCurve.FullLevel.algebraMap_jqNModC_eq_cyclicQuotientJ_of_eq_map_tatePoint_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/4685135e-37a4-504f-8f3a-347c7adf189e

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_JqCoeff

import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_forall_algebraMap_eq_cyclicQuotientJ_of_exists_of_raw_rigidDataPow
import Theorems.Thm_ModularCurve_tateBase_map_coeffMap
import Theorems.Thm_ModularCurve_exists_point_smul_tateBase_baseChange_cutOut_muTuple_of_isPrimitiveRoot
import Theorems.Thm_WeierstrassCurve_Affine_Point_zmultiples_eq_of_forall_isRoot_iff_of_addOrderOf_eq
import Theorems.Thm_ModularCurve_cyclicQuotientJ_smul_tateBase_baseChange_zmultiples_eq_algebraMap_jqNModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_algebraMap_jqNModC_eq_cyclicQuotientJ_of_eq_map_tatePoint_gamma0Pow
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero"
p2m_attr_erase "simp" "WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆"
p2m_attr_erase "simp" "TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap"
p2m_attr_erase "simp" "CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups Classical
attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

namespace TateReadingAux

theorem reading_transport {Λ : Type} [Field Λ] [DecidableEq Λ] (V V' : WeierstrassCurve Λ) (e : V = V')
    (M' d : ℕ) (h h' : ↥M'.primeFactors → Polynomial Λ) (he : h = h') (val : Λ)
    (H : ∀ g : V'.toAffine.Point,
      (addOrderOf g = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : Λ) (h₁ : V'.toAffine.Nonsingular x₁ y₁),
          n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
          (h' p).IsRoot x₁) →
      val = WeierstrassCurve.cyclicQuotientJ V' (AddSubgroup.zmultiples ((M' / d) • g)) d) :
    ∀ g : V.toAffine.Point,
      (addOrderOf g = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : Λ) (h₁ : V.toAffine.Nonsingular x₁ y₁),
          n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
          (h p).IsRoot x₁) →
      val = WeierstrassCurve.cyclicQuotientJ V (AddSubgroup.zmultiples ((M' / d) • g)) d := by
  subst e he
  exact H

theorem zmultiples_nsmul_eq_of_zmultiples_eq {G : Type*} [AddCommGroup G] {a b : G} (n : ℕ)
    (h : AddSubgroup.zmultiples a = AddSubgroup.zmultiples b) :
    AddSubgroup.zmultiples (n • a) = AddSubgroup.zmultiples (n • b) := by
  have key : ∀ {a b : G}, AddSubgroup.zmultiples a = AddSubgroup.zmultiples b →
      AddSubgroup.zmultiples (n • a) ≤ AddSubgroup.zmultiples (n • b) := by
    intro a b h
    rw [AddSubgroup.zmultiples_le]
    have ha : a ∈ AddSubgroup.zmultiples b := by rw [← h]; exact AddSubgroup.mem_zmultiples a
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp ha
    rw [← hk, smul_comm n k b]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) k
  exact le_antisymm (key h) (key h.symm)

end TateReadingAux

open TateReadingAux

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'q : ℓ' ≠ q) (hℓ'3 : 3 ≤ ℓ') (hℓ'M' : ¬ ℓ' ∣ M')
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ (q * ℓ'))
    (hιξ : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ')))
    (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK : K = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ' D →
        ModularCurve.IsLevelPStructure (C • W) ℓ' (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] [CommRing T'] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T'] (f : T →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)

    (P₀ : LevelModuliPackageAbs ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    (x₀ : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx₀ : (((WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x₀ : ↥K) : LaurentSeries ↥k₀) = ModularCurve.jqNModC ↥k₀ (q * ℓ'))
    (clC : P₀.B₀ →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j))
    (hclC : ∀ b : P₀.B₀, ((clC b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K) = P₀.classify x₀ b)

    (hμ : haveI : NeZero (q * ℓ') := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero⟩
      ∃ (C : WeierstrassCurve.VariableChange (LaurentSeries ↥k₀)) (r : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).Raw ↥K),
      (Quot.mk _ r : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K) = x₀ ∧

      (((C.u : (LaurentSeries ↥k₀)ˣ) : LaurentSeries ↥k₀) * (2 * (ModularCurve.cuspPoint ↥k₀ (q * ℓ') (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero)).unit ![1, 0]).1 + HahnSeries.C ((6 : ↥k₀)⁻¹)) =
          2 * (ModularCurve.cuspPoint ↥k₀ (q * ℓ') (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero)).unit ![1, 0]).2 + (ModularCurve.cuspPoint ↥k₀ (q * ℓ') (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero)).unit ![1, 0]).1 ∧
        C.r = HahnSeries.C (-(12 : ↥k₀)⁻¹) ∧ C.s = HahnSeries.C (-(2 : ↥k₀)⁻¹) ∧ C.t = HahnSeries.C ((24 : ↥k₀)⁻¹)) ∧

      r.curve.map (algebraMap ↥K (LaurentSeries ↥k₀)) = C • ModularCurve.tateBase ↥k₀ (q * ℓ') ∧

      (∀ (p : ↥M'.primeFactors) (F' : Type) [Field F'] (f : ↥k₀ →+* F') (ζ : F'),
        IsPrimitiveRoot ζ ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        ((r.level.1 p).map (algebraMap ↥K (LaurentSeries ↥k₀))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' (q * ℓ') (ζ ^ a)).1))) ∧

      r.level.2.1.map (algebraMap ↥K (LaurentSeries ↥k₀)) = (ModularCurve.cuspData ↥k₀ (q * ℓ') (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero)).unit ![(q : ZMod (q * ℓ')), 0] ![0, -(q : ZMod (q * ℓ'))]).variableChange C ∧

      (∃ Px Py Qx Qy : ↥K,
        (Px : LaurentSeries ↥k₀) = ((ModularCurve.cuspData ↥k₀ (q * ℓ') (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero)).unit ![(ℓ' : ZMod (q * ℓ')), 0] ![0, -(ℓ' : ZMod (q * ℓ'))]).variableChange C).xP ∧
        (Py : LaurentSeries ↥k₀) = ((ModularCurve.cuspData ↥k₀ (q * ℓ') (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero)).unit ![(ℓ' : ZMod (q * ℓ')), 0] ![0, -(ℓ' : ZMod (q * ℓ'))]).variableChange C).yP ∧
        (Qx : LaurentSeries ↥k₀) = ((ModularCurve.cuspData ↥k₀ (q * ℓ') (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero)).unit ![(ℓ' : ZMod (q * ℓ')), 0] ![0, -(ℓ' : ZMod (q * ℓ'))]).variableChange C).xQ ∧
        (Qy : LaurentSeries ↥k₀) = ((ModularCurve.cuspData ↥k₀ (q * ℓ') (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero)).unit ![(ℓ' : ZMod (q * ℓ')), 0] ![0, -(ℓ' : ZMod (q * ℓ'))]).variableChange C).yQ ∧
        IsSectionThrough r.level.2.2.P Px Py ∧ IsSectionThrough r.level.2.2.Q Qx Qy))
    :

    ∀ (d : ℕ) [NeZero d] (hd : d ∣ M')
      (hcK : ModularCurve.jqNModC ↥k₀ (q * ℓ' * d) ∈ K)
      (Ω : Type) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) Ω] [Algebra ↥K Ω]
      [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K Ω]
      (xΩ : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).Raw Ω)
      (hxΩ : (Quot.mk _ xΩ : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).Pt Ω) =
        (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map (IsScalarTower.toAlgHom ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K Ω) x₀)
      (g : (xΩ.curve).toAffine.Point)
      (hg : (addOrderOf g = M' ∧
            ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : Ω) (h₁ : (xΩ.curve).toAffine.Nonsingular x₁ y₁),
              n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
              (xΩ.level.1 p).IsRoot x₁)),
      algebraMap ↥K Ω ⟨ModularCurve.jqNModC ↥k₀ (q * ℓ' * d), hcK⟩ =
        WeierstrassCurve.cyclicQuotientJ (xΩ.curve) (AddSubgroup.zmultiples ((M' / d) • g)) d := by
  intro d _ hd hcK Ω _ _ _ _ _ _ xΩ hxΩ g hg
  have hq : (Fact.out : q.Prime).ne_zero = (Fact.out : q.Prime).ne_zero := rfl
  haveI : NeZero (q * ℓ') := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero⟩
  obtain ⟨C, r, hr, -, hcurve, htuple, -, -⟩ := hμ

  let Λ₀ : Type := AlgebraicClosure (LaurentSeries (AlgebraicClosure ℚ))
  let φK : ↥K →+* Λ₀ := (algebraMap (LaurentSeries (AlgebraicClosure ℚ)) Λ₀).comp
    ((ModularCurve.coeffMap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).comp (algebraMap ↥K (LaurentSeries ↥k₀)))
  letI instKΛ : Algebra ↥K Λ₀ := φK.toAlgebra
  letI instAΛ : Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) Λ₀ := (φK.comp (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K)).toAlgebra
  haveI : IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K Λ₀ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  let xΛ : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).Raw Λ₀ := (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K Λ₀) r
  have hxΛcl : (Quot.mk _ xΛ : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).Pt Λ₀) = (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map (IsScalarTower.toAlgHom ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K Λ₀) x₀ := by
    rw [← hr]
    show (Quot.mk _ xΛ : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).Pt Λ₀) = (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).map (IsScalarTower.toAlgHom ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K Λ₀) (Quot.mk _ r)
    rw [ModularCurve.RigidWeierstrassData.map_mk]

  let C' : WeierstrassCurve.VariableChange Λ₀ :=
    (C.map (ModularCurve.coeffMap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).map (algebraMap (LaurentSeries (AlgebraicClosure ℚ)) Λ₀)
  have hcurveΛ : xΛ.curve = C' • (ModularCurve.tateBase (AlgebraicClosure ℚ) (q * ℓ')).baseChange Λ₀ := by
    have h1 : xΛ.curve = (r.curve).map (IsScalarTower.toAlgHom ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K Λ₀).toRingHom :=
      (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).curve_mapRing (IsScalarTower.toAlgHom ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K Λ₀) r
    have h2 : (IsScalarTower.toAlgHom ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K Λ₀).toRingHom = (algebraMap (LaurentSeries (AlgebraicClosure ℚ)) Λ₀).comp
      ((ModularCurve.coeffMap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).comp (algebraMap ↥K (LaurentSeries ↥k₀))) :=
      RingHom.ext fun _ => rfl
    rw [h1, h2, ← WeierstrassCurve.map_map, ← WeierstrassCurve.map_map, hcurve, ← WeierstrassCurve.map_variableChange,
      ModularCurve.tateBase_map_coeffMap, ← WeierstrassCurve.map_variableChange]
    rfl

  have hM'K : ((M' : ℕ) : ↥K) ≠ 0 := by exact_mod_cast (NeZero.ne M')

  have hread : ∀ (g : (xΛ.curve).toAffine.Point),
      (addOrderOf g = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : Λ₀) (h₁ : (xΛ.curve).toAffine.Nonsingular x₁ y₁),
          n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
          (xΛ.level.1 p).IsRoot x₁) →
      algebraMap ↥K Λ₀ ⟨ModularCurve.jqNModC ↥k₀ (q * ℓ' * d), hcK⟩ =
        WeierstrassCurve.cyclicQuotientJ (xΛ.curve) (AddSubgroup.zmultiples ((M' / d) • g)) d := by

    have hval : algebraMap ↥K Λ₀ ⟨ModularCurve.jqNModC ↥k₀ (q * ℓ' * d), hcK⟩ =
        algebraMap (LaurentSeries (AlgebraicClosure ℚ)) Λ₀ (ModularCurve.jqNModC (AlgebraicClosure ℚ) (q * ℓ' * d)) := by
      show (algebraMap (LaurentSeries (AlgebraicClosure ℚ)) Λ₀)
          (ModularCurve.coeffMap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) (ModularCurve.jqNModC ↥k₀ (q * ℓ' * d))) = _
      rw [ModularCurve.coeffSemilinearAut.coeffMap_jqNModC]

    haveI : NeZero ((M' : ℕ) : AlgebraicClosure ℚ) := ⟨by exact_mod_cast (NeZero.ne M')⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) M'
    have hM'Q : ((M' : ℕ) : AlgebraicClosure ℚ) ≠ 0 := NeZero.ne _
    have htupleΛ : xΛ.level.1 = fun p : ↥M'.primeFactors =>
        ModularCurve.kernelVariableChangeDeg C' (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
          (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
            (Polynomial.X - Polynomial.C (algebraMap (LaurentSeries (AlgebraicClosure ℚ)) Λ₀
              (ModularCurve.toricPoint (AlgebraicClosure ℚ) (q * ℓ') ((ζ ^ (M' / (p : ℕ) ^ M'.factorization (p : ℕ))) ^ a)).1))) := by
      funext p
      have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
      have hpk : (p : ℕ) ^ M'.factorization (p : ℕ) ∣ M' := Nat.ordProj_dvd M' (p : ℕ)
      have hζp : IsPrimitiveRoot (ζ ^ (M' / (p : ℕ) ^ M'.factorization (p : ℕ))) ((p : ℕ) ^ M'.factorization (p : ℕ)) := by
        refine hζ.pow (NeZero.pos M') ?_
        exact (Nat.mul_div_cancel' hpk).symm.trans (mul_comm _ _) ▸ rfl
      have h1 : xΛ.level.1 p = ((r.level.1 p).map (algebraMap ↥K (LaurentSeries ↥k₀))).map
          ((algebraMap (LaurentSeries (AlgebraicClosure ℚ)) Λ₀).comp (ModularCurve.coeffMap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by
        show (r.level.1 p).map (IsScalarTower.toAlgHom ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K Λ₀).toRingHom = _
        rw [Polynomial.map_map]
        rfl
      rw [h1, ← Polynomial.map_map, htuple p (AlgebraicClosure ℚ) (algebraMap ↥k₀ (AlgebraicClosure ℚ)) _ hζp,
        ModularCurve.kernelVariableChangeDeg_map, Polynomial.map_prod]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rfl

    refine reading_transport _ _ hcurveΛ M' d _ _ htupleΛ _ ?_
    intro g' hg'
    obtain ⟨g₀, hg₀a, hg₀b, hg₀c, hg₀d⟩ :=
      ModularCurve.exists_point_smul_tateBase_baseChange_cutOut_muTuple_of_isPrimitiveRoot (AlgebraicClosure ℚ) Λ₀ q ℓ' M'
        hqM' hℓ'M' hM'Q ζ hζ C'

    have h0 : ∀ p : ↥M'.primeFactors, (fun p : ↥M'.primeFactors =>
        ModularCurve.kernelVariableChangeDeg C' (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
          (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
            (Polynomial.X - Polynomial.C (algebraMap (LaurentSeries (AlgebraicClosure ℚ)) Λ₀
              (ModularCurve.toricPoint (AlgebraicClosure ℚ) (q * ℓ') ((ζ ^ (M' / (p : ℕ) ^ M'.factorization (p : ℕ))) ^ a)).1)))) p ≠ 0 := by
      intro p
      simp only [ModularCurve.kernelVariableChangeDeg]
      refine mul_ne_zero (Polynomial.C_ne_zero.mpr (pow_ne_zero _ (Units.ne_zero _))) ?_
      rw [Ne, Polynomial.comp_eq_zero_iff, not_or]
      refine ⟨(Polynomial.monic_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C _).ne_zero, ?_⟩
      rintro ⟨-, h⟩
      have h2 := congrArg (Polynomial.coeff · 1) h
      simp only [← Polynomial.C_pow, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_one,
        Polynomial.coeff_C, if_neg (one_ne_zero : (1 : ℕ) ≠ 0), mul_one, add_zero] at h2
      exact (pow_ne_zero 2 (Units.ne_zero C'.u)) h2
    have hgen := WeierstrassCurve.Affine.Point.zmultiples_eq_of_forall_isRoot_iff_of_addOrderOf_eq Λ₀ _ M'
      (AddSubgroup.zmultiples g₀) ⟨inferInstance, (Nat.card_zmultiples g₀).trans hg₀c.1⟩ _ h0 hg₀d g' hg'
    rw [zmultiples_nsmul_eq_of_zmultiples_eq (M' / d) hgen, hval]
    exact (ModularCurve.cyclicQuotientJ_smul_tateBase_baseChange_zmultiples_eq_algebraMap_jqNModC (AlgebraicClosure ℚ) Λ₀
      q ℓ' M' hqM' hℓ'M' hM'Q ζ hζ C' g₀ hg₀a hg₀b d hd).symm
  exact WeierstrassCurve.DrinfeldGlobal.forall_algebraMap_eq_cyclicQuotientJ_of_exists_of_raw_rigidDataPow
    ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯 ↥K hM'K x₀ ⟨ModularCurve.jqNModC ↥k₀ (q * ℓ' * d), hcK⟩ d hd Λ₀ xΛ hxΛcl hread Ω xΩ hxΩ g hg

end S_ModularCurve_FullLevel_algebraMap_jqNModC_eq_cyclicQuotientJ_of_eq_map_tatePoint_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_algebraMap_jqNModC_eq_cyclicQuotientJ_of_eq_map_tatePoint_gamma0Pow (solution)
