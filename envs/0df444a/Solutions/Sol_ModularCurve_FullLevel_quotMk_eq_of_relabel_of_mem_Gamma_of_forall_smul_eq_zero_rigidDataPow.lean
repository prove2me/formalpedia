-- Prove2me | solution 1 for ModularCurve.FullLevel.quotMk_eq_of_relabel_of_mem_Gamma_of_forall_smul_eq_zero_rigidDataPow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/5eb1b361-ac1a-53fb-a455-0124b3bf8e3b

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
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_eq_one_of_forall_nsmul_eq_zero
import Theorems.Thm_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_eq_self_of_map_eq_one_of_isTorsionPoint
import Theorems.Thm_ModularCurve_IsLevelPStructure_relabel_relabel_and_relabel_one_and_relabel_eq_of_map_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_quotMk_eq_of_relabel_of_mem_Gamma_of_forall_smul_eq_zero_rigidDataPow
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups Classical

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace H37

theorem map_castRingHom_eq_one_of_mem_Gamma (N : ℕ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod N)) = 1 := by
  rw [CongruenceSubgroup.Gamma_mem] at hγ
  obtain ⟨h00, h01, h10, h11⟩ := hγ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply, h00, h01, h10, h11]

theorem one_map_castRingHom (N : ℕ) :
    (1 : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod N)) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem map_castRingHom_zmod_one_eq_one (g : Matrix (Fin 2) (Fin 2) ℤ) :
    g.map (Int.castRingHom (ZMod 1)) = 1 :=
  Matrix.ext fun _ _ => (ZMod.subsingleton_iff.mpr rfl).elim _ _

end H37

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
        IsCoefficientHom W f.toRingHom φ) :
    ∀ (x : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).Raw (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))),

      (∀ P : (x.curve).toAffine.Point, q • P = 0 → P = 0) →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), γ ∈ CongruenceSubgroup.Gamma ℓ' → γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ (x₁ : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).Raw (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (hΔ : IsUnit x.level.2.2.curve.Δ),
        x₁.curve = x.curve →
        x₁.level.1 = x.level.1 →
        x₁.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel x.curve
          ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.1 →
        x₁.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
          ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.2 hΔ →
        (Quot.mk _ x₁ : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).Pt (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) = Quot.mk _ x := by
  intro x hss γ hγℓ hγM x₁ hΔ hcurve hlvl1 hK hD

  have hKfix : ModularCurve.LevelRelabelling.LevelPData.relabel x.curve
      ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.1 = x.level.2.1 := by
    obtain ⟨-, h1, h3⟩ :=
      ModularCurve.IsLevelPStructure.relabel_relabel_and_relabel_one_and_relabel_eq_of_map_eq
        ℓ' hℓ'3 x.curve x.isUnit_Δ x.level.2.1 x.isLevel.2.1
    rw [h3 _ 1 (by rw [H37.map_castRingHom_eq_one_of_mem_Gamma ℓ' γ hγℓ, H37.one_map_castRingHom]), h1]

  have hDfix : ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
      ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.2 hΔ = x.level.2.2 := by
    obtain ⟨hc, hΔ', hB⟩ := x.isLevel.2.2
    obtain ⟨ev, hev⟩ := h𝒢 _ x.level.2.2.curve hΔ
    have hss' : ∀ R : (x.level.2.2.curve).toAffine.Point, q • R = 0 → R = 0 := by
      rw [hc]; exact hss
    obtain ⟨hP, hQ⟩ := WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.eq_one_of_forall_nsmul_eq_zero
      x.level.2.2.curve hΔ (𝒢 _ x.level.2.2.curve hΔ) ev hev q hss' x.level.2.2.P x.level.2.2.Q hB
    refine ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel_eq_self_of_map_eq_one_of_isTorsionPoint 𝒢
      x.level.2.2 hΔ 1 ?_ ?_ _ (H37.map_castRingHom_zmod_one_eq_one _)
    · rw [WeierstrassProjModel.RelativeGroupLaw.isTorsionPoint_one_iff]; exact hP
    · rw [WeierstrassProjModel.RelativeGroupLaw.isTorsionPoint_one_iff]; exact hQ

  have hx : x₁ = x :=
    LevelComponent.Raw.ext' hcurve (Prod.ext hlvl1 (Prod.ext (hK.trans hKfix) (hD.trans hDfix)))
  rw [hx]

end S_ModularCurve_FullLevel_quotMk_eq_of_relabel_of_mem_Gamma_of_forall_smul_eq_zero_rigidDataPow
end P2MW
export P2MW.S_ModularCurve_FullLevel_quotMk_eq_of_relabel_of_mem_Gamma_of_forall_smul_eq_zero_rigidDataPow (solution)
