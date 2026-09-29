-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_raw_etale_map_eq_map_qExpand_of_tatePoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/79bb7bea-db1e-5003-ab0a-d0434c440e48

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
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
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_ModularCurve_ModuliPointMap
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Theorems.Thm_ModularCurve_tateBase_mul_eq_map_qExpand_and_tateToricPoint_eq_and_nonToricPoint_eq
import Theorems.Thm_ModularCurve_FullLevel_exists_variableChange_raw_etale_tate_weightOne_level_fst_gamma0Pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_raw_etale_map_eq_map_qExpand_of_tatePoint
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups Classical
open CategoryTheory AlgebraicGeometry

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace F2Aux

theorem coeff_tateToricPoint_fst_self (R : Type*) [CommRing R] (p : ℕ) [NeZero p] (c : Rˣ) :
    ((ModularCurve.tateToricPoint R p c).1).coeff (p : ℤ) = (c : R) + ((c⁻¹ : Rˣ) : R) - 2 := by
  have hp : p ≠ 0 := NeZero.ne p
  rw [ModularCurve.tateToricPoint_fst, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk, if_neg hp]
  rw [Finset.sum_eq_single_of_mem p (Nat.mem_divisors_self p hp)]
  · rw [if_pos dvd_rfl, if_pos dvd_rfl, Nat.div_self (Nat.pos_of_ne_zero hp), Nat.divisors_one]
    simp
  · intro d hd hdp
    rw [if_neg]
    intro hpd
    exact hdp (Nat.dvd_antisymm (Nat.dvd_of_mem_divisors hd) hpd)

theorem coeff_tateToricPoint_snd_self (R : Type*) [CommRing R] (p : ℕ) [NeZero p] (c : Rˣ) :
    ((ModularCurve.tateToricPoint R p c).2).coeff (p : ℤ) = 1 - ((c⁻¹ : Rˣ) : R) := by
  have hp : p ≠ 0 := NeZero.ne p
  rw [ModularCurve.tateToricPoint_snd, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk, if_neg hp]
  rw [Finset.sum_eq_single_of_mem p (Nat.mem_divisors_self p hp)]
  · rw [if_pos dvd_rfl, if_pos dvd_rfl, Nat.div_self (Nat.pos_of_ne_zero hp), Nat.divisors_one]
    simp
    ring
  · intro d hd hdp
    rw [if_neg]
    intro hpd
    exact hdp (Nat.dvd_antisymm (Nat.dvd_of_mem_divisors hd) hpd)

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N]
    (x : LaurentSeries R) :
    ModularCurve.coeffMap f (ModularCurve.qExpand R N x) = ModularCurve.qExpand S N (ModularCurve.coeffMap f x) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [ModularCurve.coeffMap_coeff, ModularCurve.qExpand_coeff_mul, ModularCurve.qExpand_coeff_mul,
      ModularCurve.coeffMap_coeff]
  · rw [ModularCurve.coeffMap_coeff, ModularCurve.qExpand_coeff_of_not_dvd N _ hk,
      ModularCurve.qExpand_coeff_of_not_dvd N _ hk, map_zero]

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (ModularCurve.coeffMap f) := by
  intro x y h
  ext k
  apply hf
  rw [← ModularCurve.coeffMap_coeff, ← ModularCurve.coeffMap_coeff, h]

end F2Aux

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)

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

    (x₀ : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx₀ : (((WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x₀ : ↥K) : LaurentSeries ↥k₀) = ModularCurve.jqNModC ↥k₀ (q * ℓ'))
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

    (K'' : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK'' : K'' = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M')))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K''] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K''] :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    ∃ (r : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).Raw ↥K)
      (r'' : (((ModularCurve.gamma0PowComponent ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) M' hM).prod ((ModularCurve.levelPComponent ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' hℓ).prod (ModularCurve.LevelComponent.trivial (A := ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))))).toRigid).Raw ↥K''),
      (Quot.mk _ r : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K) = x₀ ∧

      r.curve.map (algebraMap ↥K (LaurentSeries ↥k₀)) = r''.curve.map ((ModularCurve.qExpand ↥k₀ q).comp (algebraMap ↥K'' (LaurentSeries ↥k₀))) ∧

      (∀ p : ↥M'.primeFactors, (r.level.1 p).map (algebraMap ↥K (LaurentSeries ↥k₀)) = (r''.level.1 p).map ((ModularCurve.qExpand ↥k₀ q).comp (algebraMap ↥K'' (LaurentSeries ↥k₀)))) ∧

      r.level.2.1.map (algebraMap ↥K (LaurentSeries ↥k₀)) = r''.level.2.1.map ((ModularCurve.qExpand ↥k₀ q).comp (algebraMap ↥K'' (LaurentSeries ↥k₀))) := by
  haveI hNq : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hqℓ0 : q * ℓ' ≠ 0 := Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero
  haveI hNqℓ : NeZero (q * ℓ') := ⟨hqℓ0⟩
  haveI hNℓ : NeZero ℓ' := ⟨(Fact.out : ℓ'.Prime).ne_zero⟩
  haveI : Fact (1 < ℓ') := ⟨(Fact.out : ℓ'.Prime).one_lt⟩
  haveI : Fact (1 < q * ℓ') := ⟨by nlinarith [(Fact.out : ℓ'.Prime).one_lt, (Fact.out : q.Prime).one_lt]⟩
  have hqlt : q < q * ℓ' := by nlinarith [(Fact.out : ℓ'.Prime).one_lt, (Fact.out : q.Prime).one_lt]

  obtain ⟨C, r₀, hr₀, ⟨hCu, hCr, hCs, hCt⟩, hcurve, hG0, hKatz, -⟩ := hμ

  have hζ' : IsPrimitiveRoot (ξ ^ q) ℓ' := hξ.pow (Nat.pos_of_ne_zero hqℓ0) rfl
  have hιζ' : ∃ ι : ↥k₀ →+* ℂ, ι (ξ ^ q) = Complex.exp (2 * Real.pi * Complex.I / ℓ') := by
    obtain ⟨ι, hι⟩ := hιξ
    refine ⟨ι, ?_⟩
    rw [map_pow, hι, ← Complex.exp_nat_mul]
    congr 1
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    field_simp
  obtain ⟨C₁, x'', ⟨hC₁u, hC₁r, hC₁s, hC₁t⟩, hcurve'', hG0'', hKatz''⟩ :=
    ModularCurve.FullLevel.exists_variableChange_raw_etale_tate_weightOne_level_fst_gamma0Pow
      M' ℓ' hℓ'3 hℓ'M' ↥k₀ (ξ ^ q) hζ' hιζ' K'' hK'' ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) hℓ hM

  obtain ⟨hTB, hTor, hNon⟩ :=
    ModularCurve.tateBase_mul_eq_map_qExpand_and_tateToricPoint_eq_and_nonToricPoint_eq ↥k₀ ℓ' q

  set LS := LaurentSeries ↥k₀ with hLS
  set ι : ↥K →+* LS := algebraMap ↥K LS with hι
  set qE : LS →+* LS := ModularCurve.qExpand ↥k₀ q with hqE
  set ι'' : ↥K'' →+* LS := algebraMap ↥K'' LS with hι''
  set ξu : (↥k₀)ˣ := (hξ.isUnit hqℓ0).unit with hξu
  set ζu : (↥k₀)ˣ := (hζ'.isUnit (Fact.out : ℓ'.Prime).ne_zero).unit with hζu
  have hξuq : ξu ^ q = ζu := Units.ext (by simp [hξu, hζu, IsUnit.unit_spec])

  set xq : LS := (ModularCurve.cuspPoint ↥k₀ (q * ℓ') ξu ![(q : ZMod (q * ℓ')), 0]).1 with hxq
  set yq : LS := (ModularCurve.cuspPoint ↥k₀ (q * ℓ') ξu ![(q : ZMod (q * ℓ')), 0]).2 with hyq
  set x1 : LS := (ModularCurve.cuspPoint ↥k₀ ℓ' ζu ![(1 : ZMod ℓ'), 0]).1 with hx1
  set y1 : LS := (ModularCurve.cuspPoint ↥k₀ ℓ' ζu ![(1 : ZMod ℓ'), 0]).2 with hy1
  have hcq : ModularCurve.cuspPoint ↥k₀ (q * ℓ') ξu ![(q : ZMod (q * ℓ')), 0] = ModularCurve.tateToricPoint ↥k₀ (q * ℓ') ζu := by
    rw [ModularCurve.cuspPoint_of_eq_zero ξu (by simp)]
    congr 1
    rw [← hξuq]; congr 1
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hqlt]
  have hc1 : ModularCurve.cuspPoint ↥k₀ ℓ' ζu ![(1 : ZMod ℓ'), 0] = ModularCurve.tateToricPoint ↥k₀ ℓ' ζu := by
    rw [ModularCurve.cuspPoint_of_eq_zero ζu (by simp)]
    congr 1
    simp [ZMod.val_one]
  have hxq1 : xq = qE x1 := by
    simp only [hxq, hx1, hcq, hc1, hqE]; exact (hTor ζu).1
  have hyq1 : yq = qE y1 := by
    simp only [hyq, hy1, hcq, hc1, hqE]; exact (hTor ζu).2

  set X : ↥K := r₀.level.2.1.xP with hX
  set Y : ↥K := r₀.level.2.1.yP with hY
  have hιX : ι X = ((ModularCurve.cuspData ↥k₀ (q * ℓ') ξu ![(q : ZMod (q * ℓ')), 0] ![0, -(q : ZMod (q * ℓ'))]).variableChange C).xP := by
    have := congrArg ModularCurve.LevelPData.xP hKatz
    simpa [ModularCurve.LevelPData.map_xP] using this
  have hιY : ι Y = ((ModularCurve.cuspData ↥k₀ (q * ℓ') ξu ![(q : ZMod (q * ℓ')), 0] ![0, -(q : ZMod (q * ℓ'))]).variableChange C).yP := by
    have := congrArg ModularCurve.LevelPData.yP hKatz
    simpa [ModularCurve.LevelPData.map_yP] using this

  haveI : CharZero ↥k₀ := charZero_of_injective_algebraMap (algebraMap ℚ ↥k₀).injective
  have hζ1 : (ξ : ↥k₀) ^ q ≠ 1 := hζ'.ne_one (Fact.out : ℓ'.Prime).one_lt
  have hζsq : ((ξ : ↥k₀) ^ q) ^ 2 ≠ 1 := by
    intro h
    have := (hζ'.pow_eq_one_iff_dvd 2).mp h
    have : ℓ' ≤ 2 := Nat.le_of_dvd two_pos this
    omega
  have hζu_val : ((ζu : (↥k₀)ˣ) : ↥k₀) = ξ ^ q := by simp [hζu, IsUnit.unit_spec]
  have hζ0 : (ξ : ↥k₀) ^ q ≠ 0 := hζ'.ne_zero (Fact.out : ℓ'.Prime).ne_zero
  have hinv : (ξ : ↥k₀) ^ q * ((ξ : ↥k₀) ^ q)⁻¹ = 1 := mul_inv_cancel₀ hζ0
  set a : LS := xq - C.r with ha
  set b : LS := 2 * yq + xq with hb
  have hcoeffC : ∀ (r : ↥k₀), (HahnSeries.C r : LS).coeff ((q * ℓ' : ℕ) : ℤ) = 0 := by
    intro r
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne]
    exact_mod_cast hqℓ0
  have ha0 : a ≠ 0 := by
    intro h0
    have h0' : xq = C.r := sub_eq_zero.mp (by rw [ha] at h0; exact h0)
    have h1 := congrArg (fun z : LS => z.coeff ((q * ℓ' : ℕ) : ℤ)) h0'
    simp only [hxq, hcq, hCr, hcoeffC, F2Aux.coeff_tateToricPoint_fst_self, hζu_val,
      Units.val_inv_eq_inv_val] at h1
    apply hζ1
    have h2 : ((ξ : ↥k₀) ^ q - 1) ^ 2 = 0 := by linear_combination (ξ ^ q) * h1 - hinv
    exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2)
  have hC2' : (2 : LS) = HahnSeries.C (2 : ↥k₀) := (map_ofNat HahnSeries.C 2).symm
  have hb0 : b ≠ 0 := by
    intro h0
    have h0' : (2 : ↥k₀) • yq = -xq := by
      rw [← HahnSeries.C_mul_eq_smul, ← hC2']; exact eq_neg_of_add_eq_zero_left (by rw [hb] at h0; exact h0)
    have h1 := congrArg (fun z : LS => z.coeff ((q * ℓ' : ℕ) : ℤ)) h0'
    have e1 : (((2 : ↥k₀) • yq).coeff ((q * ℓ' : ℕ) : ℤ) : ↥k₀) = 2 * yq.coeff ((q * ℓ' : ℕ) : ℤ) :=
      HahnSeries.coeff_smul
    have e2 : ((-xq).coeff ((q * ℓ' : ℕ) : ℤ) : ↥k₀) = -(xq.coeff ((q * ℓ' : ℕ) : ℤ)) := HahnSeries.coeff_neg
    simp only [e1, e2] at h1
    simp only [hxq, hyq, hcq, F2Aux.coeff_tateToricPoint_fst_self, F2Aux.coeff_tateToricPoint_snd_self, hζu_val,
      Units.val_inv_eq_inv_val] at h1
    apply hζsq
    have h2 : ((ξ : ↥k₀) ^ q) ^ 2 - 1 = 0 := by linear_combination (ξ ^ q) * h1 + hinv
    exact sub_eq_zero.mp h2

  have hC2 : (2 : LS) = HahnSeries.C (2 : ↥k₀) := hC2'
  have hs2 : (2 : LS) * C.s = -1 := by
    rw [hCs, hC2, ← map_mul, show (2 : ↥k₀) * -2⁻¹ = -1 by norm_num, map_neg, map_one]
  have ht2 : (2 : LS) * C.t + C.r = 0 := by
    rw [hCt, hCr, hC2, ← map_mul, ← map_add, show (2 : ↥k₀) * 24⁻¹ + -12⁻¹ = 0 by norm_num, map_zero]
  have hr6 : (HahnSeries.C ((6 : ↥k₀)⁻¹) : LS) = -2 * C.r := by
    rw [hCr, hC2, neg_mul, ← map_mul, ← map_neg, show -((2 : ↥k₀) * -12⁻¹) = 6⁻¹ by norm_num]
  have h2a : 2 * xq + HahnSeries.C ((6 : ↥k₀)⁻¹) = 2 * a := by rw [hr6, ha]; ring
  have h2B : 2 * (yq - C.s * a - C.t) = b := by
    rw [hb, ha]; linear_combination (-(xq - C.r)) * hs2 - ht2
  have hB0 : yq - C.s * a - C.t ≠ 0 := by
    intro h; apply hb0; rw [← h2B, h, mul_zero]

  have hιX' : ι X = (((C.u⁻¹ : LSˣ)) : LS) ^ 2 * a := by
    rw [hιX]; simp only [ModularCurve.LevelPData.variableChange_xP, ModularCurve.cuspData, ha, hxq]
  have hιY' : ι Y = (((C.u⁻¹ : LSˣ)) : LS) ^ 3 * (yq - C.s * a - C.t) := by
    rw [hιY]; simp only [ModularCurve.LevelPData.variableChange_yP, ModularCurve.cuspData, ha, hxq, hyq]
  have hU0 : (((C.u⁻¹ : LSˣ)) : LS) ≠ 0 := Units.ne_zero _
  have hX0 : X ≠ 0 := by
    intro h; have := hιX'; rw [h, map_zero] at this
    exact (mul_ne_zero (pow_ne_zero 2 hU0) ha0) this.symm
  have hY0 : Y ≠ 0 := by
    intro h; have := hιY'; rw [h, map_zero] at this
    exact (mul_ne_zero (pow_ne_zero 3 hU0) hB0) this.symm

  set w : ↥K := Y / X with hw
  have hw0 : w ≠ 0 := div_ne_zero hY0 hX0
  have hu₁ : qE ((C₁.u : LSˣ) : LS) * (2 * a) = b := by
    have := congrArg qE hC₁u
    rw [map_mul, map_add, map_add, map_mul, map_mul, ← hxq1, ← hyq1, hqE, ModularCurve.qExpand_C, map_ofNat] at this
    rw [← h2a, hb]; exact this
  have ha20 : (2 : LS) * a ≠ 0 := by
    refine mul_ne_zero ?_ ha0
    rw [hC2]; exact (map_ne_zero_iff _ HahnSeries.C_injective).mpr two_ne_zero
  have hwu : ι w * ((C.u : LSˣ) : LS) = qE ((C₁.u : LSˣ) : LS) := by
    have hUV : ((C.u : LSˣ) : LS) * (((C.u⁻¹ : LSˣ)) : LS) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hιX0 : ι X ≠ 0 := by rw [hιX']; exact mul_ne_zero (pow_ne_zero 2 hU0) ha0
    have e : ι w * ι X = ι Y := by rw [hw, map_div₀]; exact div_mul_cancel₀ _ hιX0
    apply mul_right_cancel₀ hιX0
    apply mul_right_cancel₀ ha20
    calc ι w * ((C.u : LSˣ) : LS) * ι X * (2 * a)
        = (ι w * ι X) * ((C.u : LSˣ) : LS) * (2 * a) := by ring
      _ = ι Y * ((C.u : LSˣ) : LS) * (2 * a) := by rw [e]
      _ = (((C.u⁻¹ : LSˣ)) : LS) ^ 3 * (yq - C.s * a - C.t) * ((C.u : LSˣ) : LS) * (2 * a) := by rw [hιY']
      _ = ((((C.u⁻¹ : LSˣ)) : LS) ^ 2 * a) * (2 * (yq - C.s * a - C.t)) *
            (((C.u : LSˣ) : LS) * (((C.u⁻¹ : LSˣ)) : LS)) := by ring
      _ = ι X * b * 1 := by rw [hιX', h2B, hUV]
      _ = ι X * (qE ((C₁.u : LSˣ) : LS) * (2 * a)) := by rw [hu₁, mul_one]
      _ = qE ((C₁.u : LSˣ) : LS) * ((2 : LS) * a)⁻¹⁻¹ * ι X := by rw [inv_inv]; ring
      _ = qE ((C₁.u : LSˣ) : LS) * ι X * (2 * a) := by rw [inv_inv]; ring

  set D : WeierstrassCurve.VariableChange ↥K := ⟨Units.mk0 w hw0, 0, 0, 0⟩ with hD
  have hVC : D.map ι * C = C₁.map qE := by
    refine WeierstrassCurve.VariableChange.ext (Units.ext ?_) ?_ ?_ ?_
    · simp only [WeierstrassCurve.VariableChange.mul_def, WeierstrassCurve.VariableChange.map, hD,
        Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_mk0]
      exact hwu
    · simp only [WeierstrassCurve.VariableChange.mul_def, WeierstrassCurve.VariableChange.map_r,
        WeierstrassCurve.VariableChange.map_u, hD, map_zero, zero_mul, zero_add, hCr, hC₁r, hqE]
      exact (ModularCurve.qExpand_C q _).symm
    · simp only [WeierstrassCurve.VariableChange.mul_def, WeierstrassCurve.VariableChange.map_s,
        WeierstrassCurve.VariableChange.map_u, hD, map_zero, mul_zero, zero_add, hCs, hC₁s, hqE]
      exact (ModularCurve.qExpand_C q _).symm
    · simp only [WeierstrassCurve.VariableChange.mul_def, WeierstrassCurve.VariableChange.map_t,
        WeierstrassCurve.VariableChange.map_r, WeierstrassCurve.VariableChange.map_u, hD, map_zero, zero_mul,
        zero_add, hCt, hC₁t, hqE]
      exact (ModularCurve.qExpand_C q _).symm

  refine ⟨(WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).act D r₀, x'', ?_, ?_, ?_, ?_⟩
  ·
    rw [← hr₀]
    exact (Quot.sound ⟨D, rfl⟩).symm
  ·
    have hc : ((WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).act D r₀).curve = D • r₀.curve := rfl
    rw [hc, ← WeierstrassCurve.map_variableChange, hcurve, ← mul_smul, hVC, ← WeierstrassCurve.map_map, hcurve'',
      ← WeierstrassCurve.map_variableChange, hqE, ← hTB]
  ·
    intro p
    obtain ⟨ι₀, -⟩ := hιξ
    set d : ℕ := ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)) with hd
    set n : ℕ := (p : ℕ) ^ M'.factorization (p : ℕ) with hn
    have hn0 : n ≠ 0 := pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).ne_zero
    have hζC : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / n)) n := Complex.isPrimitiveRoot_exp n hn0
    set ζC : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hζCdef
    have hζC0 : ζC ≠ 0 := hζC.ne_zero hn0
    have hcfinj : Function.Injective (ModularCurve.coeffMap ι₀ : LS →+* LaurentSeries ℂ) :=
      F2Aux.coeffMap_injective ι₀ ι₀.injective
    have e1 := hG0 p ℂ ι₀ ζC hζC
    have e2 := hG0'' p ℂ ι₀ ζC hζC
    have hlvl : ((WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).act D r₀).level.1 p = ModularCurve.kernelVariableChangeDeg D d (r₀.level.1 p) := rfl

    have hcomm : (ModularCurve.coeffMap ι₀ : LS →+* LaurentSeries ℂ).comp qE =
        (ModularCurve.qExpand ℂ q).comp (ModularCurve.coeffMap ι₀) :=
      RingHom.ext fun x => by simp only [RingHom.comp_apply, hqE]; exact F2Aux.coeffMap_qExpand ι₀ q x
    have hmapmul : ∀ (C C' : WeierstrassCurve.VariableChange LS) (φ : LS →+* LaurentSeries ℂ),
        (C * C').map φ = C.map φ * C'.map φ := fun C C' φ => (WeierstrassCurve.VariableChange.mapHom φ).map_mul C C'

    obtain ⟨-, hTorC, -⟩ := ModularCurve.tateBase_mul_eq_map_qExpand_and_tateToricPoint_eq_and_nonToricPoint_eq ℂ ℓ' q
    have hprod : (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
          (Polynomial.X - Polynomial.C (ModularCurve.toricPoint ℂ ℓ' (ζC ^ a)).1)).map (ModularCurve.qExpand ℂ q) =
        ∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
          (Polynomial.X - Polynomial.C (ModularCurve.toricPoint ℂ (q * ℓ') (ζC ^ a)).1) := by
      rw [Polynomial.map_prod]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      congr 2
      have hu : IsUnit (ζC ^ a) := isUnit_iff_ne_zero.mpr (pow_ne_zero _ hζC0)
      rw [← hu.unit_spec, ← ModularCurve.tateToricPoint_eq_toricPoint, ← ModularCurve.tateToricPoint_eq_toricPoint]
      exact ((hTorC hu.unit).1).symm
    apply Polynomial.map_injective (ModularCurve.coeffMap ι₀) hcfinj
    rw [hlvl, ModularCurve.kernelVariableChangeDeg_map, ModularCurve.kernelVariableChangeDeg_map, e1,
      ← ModularCurve.kernelVariableChangeDeg_mul, ← hmapmul, hVC]

    rw [Polynomial.map_map, ← RingHom.comp_assoc, hcomm, RingHom.comp_assoc, ← Polynomial.map_map,
      ← Polynomial.map_map, e2, ModularCurve.kernelVariableChangeDeg_map, hprod,
      WeierstrassCurve.VariableChange.map_map, WeierstrassCurve.VariableChange.map_map, hcomm]
  ·
    have hlvl : ((WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).act D r₀).level.2.1 = ModularCurve.LevelPData.variableChange D r₀.level.2.1 := rfl
    rw [hlvl, ModularCurve.LevelPData.map_variableChange, hKatz, ← ModularCurve.LevelPData.variableChange_mul, hVC,
      ← ModularCurve.LevelPData.map_map, hKatz'', ModularCurve.LevelPData.map_variableChange]
    congr 1

    have hnq : ModularCurve.cuspPoint ↥k₀ (q * ℓ') ξu ![0, -(q : ZMod (q * ℓ'))] = ModularCurve.nonToricPoint ↥k₀ (q * ℓ') 1 (q * ℓ' - q) := by
      have hq0' : (q : ZMod (q * ℓ')) ≠ 0 := by
        intro h
        have := congrArg ZMod.val h
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hqlt, ZMod.val_zero] at this
        exact (Fact.out : q.Prime).ne_zero this
      have hne : (![0, -(q : ZMod (q * ℓ'))] : Fin 2 → ZMod (q * ℓ')) 1 ≠ 0 := by
        simpa using hq0'
      rw [ModularCurve.cuspPoint_of_ne_zero ξu hne]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, ZMod.val_zero, pow_zero]
      congr 1
      rw [ZMod.neg_val, if_neg hq0', ZMod.val_natCast, Nat.mod_eq_of_lt hqlt]
    have hn1 : ModularCurve.cuspPoint ↥k₀ ℓ' ζu ![0, -(1 : ZMod ℓ')] = ModularCurve.nonToricPoint ↥k₀ ℓ' 1 (ℓ' - 1) := by
      have hne : (![0, -(1 : ZMod ℓ')] : Fin 2 → ZMod ℓ') 1 ≠ 0 := by
        simp
      rw [ModularCurve.cuspPoint_of_ne_zero ζu hne]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, ZMod.val_zero, pow_zero]
      congr 1
      rw [ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one]
    have hℓ1 : 0 < ℓ' - 1 := by omega
    have hℓ2 : ℓ' - 1 < ℓ' := by omega
    obtain ⟨hN1, hN2⟩ := hNon 1 (ℓ' - 1) hℓ1 hℓ2
    have hqq : q * (ℓ' - 1) = q * ℓ' - q := Nat.mul_sub_one q ℓ'
    refine ModularCurve.LevelPData.ext ?_ ?_ ?_ ?_
    · rw [ModularCurve.LevelPData.map_xP]
      exact (show (ModularCurve.cuspPoint ↥k₀ (q * ℓ') ξu ![(q : ZMod (q * ℓ')), 0]).1 =
        qE (ModularCurve.cuspPoint ↥k₀ ℓ' ζu ![(1 : ZMod ℓ'), 0]).1 from hxq1)
    · rw [ModularCurve.LevelPData.map_yP]
      exact (show (ModularCurve.cuspPoint ↥k₀ (q * ℓ') ξu ![(q : ZMod (q * ℓ')), 0]).2 =
        qE (ModularCurve.cuspPoint ↥k₀ ℓ' ζu ![(1 : ZMod ℓ'), 0]).2 from hyq1)
    · rw [ModularCurve.LevelPData.map_xQ]
      show (ModularCurve.cuspPoint ↥k₀ (q * ℓ') ξu ![0, -(q : ZMod (q * ℓ'))]).1 =
        qE (ModularCurve.cuspPoint ↥k₀ ℓ' ζu ![0, -(1 : ZMod ℓ')]).1
      rw [hn1, hnq, ← hqq, hqE]; exact hN1
    · rw [ModularCurve.LevelPData.map_yQ]
      show (ModularCurve.cuspPoint ↥k₀ (q * ℓ') ξu ![0, -(q : ZMod (q * ℓ'))]).2 =
        qE (ModularCurve.cuspPoint ↥k₀ ℓ' ζu ![0, -(1 : ZMod ℓ')]).2
      rw [hn1, hnq, ← hqq, hqE]; exact hN2

end S_ModularCurve_FullLevel_exists_raw_etale_map_eq_map_qExpand_of_tatePoint
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_raw_etale_map_eq_map_qExpand_of_tatePoint (solution)
