-- Prove2me | solution 1 for ModularCurve.exists_map_eq_and_isLevelPStructure_of_isLevelPStructure_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/826923f9-3af5-54fa-a183-3caffdf15e12

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_EllipticCurve_PointReduction
import Theorems.Thm_WeierstrassCurve_mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero
import Theorems.Thm_WeierstrassCurve_eq_zero_of_smul_eq_zero_of_reducePoint_eq_zero
import Theorems.Thm_WeierstrassCurve_reducePoint_add
import Theorems.Thm_WeierstrassCurve_reducePoint_some
import Theorems.Thm_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_map_eq_and_isLevelPStructure_of_isLevelPStructure_map
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

universe u

namespace LevelPExtendsAux

open WeierstrassCurve IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

variable {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
  {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]

theorem hasGoodReduction_map (W₀ : WeierstrassCurve R₀) (hΔ₀ : IsUnit W₀.Δ) :
    (W₀.map (algebraMap R₀ K)).HasGoodReduction R₀ := by
  have hint : ∀ C : WeierstrassCurve.VariableChange K, C = 1 → (C • W₀.map (algebraMap R₀ K)).IsIntegral R₀ := by
    rintro C rfl; rw [one_smul]; exact ⟨W₀, rfl⟩
  haveI hI : (W₀.map (algebraMap R₀ K)).IsIntegral R₀ := ⟨W₀, rfl⟩
  have hval : valuation K (maximalIdeal R₀) (W₀.map (algebraMap R₀ K)).Δ = 1 := by
    rw [WeierstrassCurve.map_Δ]
    apply le_antisymm (valuation_le_one _ _)
    rw [← not_lt, valuation_lt_one_iff_mem]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).mp h hΔ₀
  haveI hmin : (W₀.map (algebraMap R₀ K)).IsMinimal R₀ := by
    refine ⟨⟨by show WeierstrassCurve.IsIntegral R₀ ((1 : WeierstrassCurve.VariableChange K) • W₀.map (algebraMap R₀ K)); rw [one_smul]; exact hI, ?_⟩⟩
    intro C _ _
    show valuation_Δ_aux R₀ (C • W₀.map (algebraMap R₀ K)) ≤
      valuation_Δ_aux R₀ ((1 : WeierstrassCurve.VariableChange K) • W₀.map (algebraMap R₀ K))
    have h1 : valuation_Δ_aux R₀ ((1 : WeierstrassCurve.VariableChange K) • W₀.map (algebraMap R₀ K)) =
        ⟨1, le_rfl⟩ := by
      apply Subtype.ext
      haveI : ((1 : WeierstrassCurve.VariableChange K) • W₀.map (algebraMap R₀ K)).IsIntegral R₀ := hint 1 rfl
      rw [valuation_Δ_aux_eq_of_isIntegral]
      show valuation K (maximalIdeal R₀) ((1 : WeierstrassCurve.VariableChange K) • W₀.map (algebraMap R₀ K)).Δ = 1
      rw [one_smul]; exact hval
    rw [h1]
    exact (valuation_Δ_aux R₀ (C • W₀.map (algebraMap R₀ K))).2
  exact ⟨hval⟩

theorem integralModel_map (W₀ : WeierstrassCurve R₀) [hI : (W₀.map (algebraMap R₀ K)).IsIntegral R₀] :
    integralModel R₀ (W₀.map (algebraMap R₀ K)) = W₀ :=
  WeierstrassCurve.map_injective (IsFractionRing.injective R₀ K)
    (baseChange_integralModel_eq R₀ (W₀.map (algebraMap R₀ K)))

theorem reduceCoord_algebraMap (r : R₀) : reduceCoord R₀ (algebraMap R₀ K r) = residue R₀ r := by
  classical
  unfold reduceCoord
  have h : ∃ r' : R₀, algebraMap R₀ K r' = algebraMap R₀ K r := ⟨r, rfl⟩
  rw [dif_pos h]
  congr 1
  exact IsFractionRing.injective R₀ K h.choose_spec

noncomputable def reduceHom' (W : WeierstrassCurve K) [DecidableEq K] [W.HasGoodReduction R₀]
    [DecidableEq (ResidueField R₀)] : W.toAffine.Point →+ (W.reduction R₀).toAffine.Point where
  toFun := reducePoint_alt R₀ W
  map_zero' := rfl
  map_add' := WeierstrassCurve.reducePoint_add R₀ W

end LevelPExtendsAux

open LevelPExtendsAux WeierstrassCurve IsLocalRing IsDedekindDomain.HeightOneSpectrum in

theorem solution
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (W₀ : WeierstrassCurve R₀) (hΔ₀ : IsUnit W₀.Δ) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : R₀))
    (D' : ModularCurve.LevelPData K) (hD' : ModularCurve.IsLevelPStructure (W₀.map (algebraMap R₀ K)) ℓ D') :
    ∃ D₀ : ModularCurve.LevelPData R₀, D₀.map (algebraMap R₀ K) = D' ∧ ModularCurve.IsLevelPStructure W₀ ℓ D₀ := by
  classical
  have hinj : Function.Injective (algebraMap R₀ K) := IsFractionRing.injective R₀ K
  set W := W₀.map (algebraMap R₀ K) with hW

  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    have h := hD'.preΨ_P
    rw [show ((W₀.map (algebraMap R₀ K)).preΨ (2 : ℕ)) = 1 from WeierstrassCurve.preΨ_two _, Polynomial.eval_one] at h
    exact one_ne_zero h
  have hℓodd : Odd ℓ := (Fact.out : ℓ.Prime).odd_of_ne_two hℓ2

  obtain ⟨⟨xP₀, hxP⟩, ⟨yP₀, hyP⟩⟩ :=
    WeierstrassCurve.mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero W₀ ℓ hℓ D'.xP D'.yP hD'.equation_P hD'.preΨ_P
  obtain ⟨⟨xQ₀, hxQ⟩, ⟨yQ₀, hyQ⟩⟩ :=
    WeierstrassCurve.mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero W₀ ℓ hℓ D'.xQ D'.yQ hD'.equation_Q hD'.preΨ_Q
  refine ⟨⟨xP₀, yP₀, xQ₀, yQ₀⟩, ?_, ?_⟩
  · ext <;> simp [ModularCurve.LevelPData.map, hxP, hyP, hxQ, hyQ]

  have heqP : W₀.toAffine.Equation xP₀ yP₀ := by
    rw [← WeierstrassCurve.Affine.map_equation _ hinj, hxP, hyP]; exact hD'.equation_P
  have heqQ : W₀.toAffine.Equation xQ₀ yQ₀ := by
    rw [← WeierstrassCurve.Affine.map_equation _ hinj, hxQ, hyQ]; exact hD'.equation_Q
  have hψP : (W₀.preΨ ℓ).eval xP₀ = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← WeierstrassCurve.map_preΨ, hxP]
    exact hD'.preΨ_P
  have hψQ : (W₀.preΨ ℓ).eval xQ₀ = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← WeierstrassCurve.map_preΨ, hxQ]
    exact hD'.preΨ_Q

  haveI hGR : W.HasGoodReduction R₀ := hasGoodReduction_map W₀ hΔ₀
  haveI : W.IsElliptic := ⟨by rw [hW, WeierstrassCurve.map_Δ]; exact (hΔ₀.map _)⟩
  have hmodel : integralModel R₀ W = W₀ := integralModel_map W₀
  have hred : W.reduction R₀ = W₀.map (residue R₀) := by
    show (integralModel R₀ W).map (residue R₀) = _; rw [hmodel]
  have hℓk : ((ℓ : ℕ) : ResidueField R₀) ≠ 0 := by
    rw [← map_natCast (residue R₀)]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hℓ
  haveI : Fact ℓ.Prime := inferInstance

  have hnsP : W.toAffine.Nonsingular D'.xP D'.yP := (W.toAffine.equation_iff_nonsingular).mp hD'.equation_P
  have hnsQ : W.toAffine.Nonsingular D'.xQ D'.yQ := (W.toAffine.equation_iff_nonsingular).mp hD'.equation_Q
  set P : W.toAffine.Point := .some D'.xP D'.yP hnsP with hPdef
  set Q : W.toAffine.Point := .some D'.xQ D'.yQ hnsQ with hQdef
  have hℓP : ℓ • P = 0 := by
    rw [hPdef, WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hℓodd]
    rw [← WeierstrassCurve.preΨ_ofNat]; exact hD'.preΨ_P
  have hℓQ : ℓ • Q = 0 := by
    rw [hQdef, WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hℓodd]
    rw [← WeierstrassCurve.preΨ_ofNat]; exact hD'.preΨ_Q

  have hvP : valuation K (IsDiscreteValuationRing.maximalIdeal R₀) D'.xP ≤ 1 ∧
      valuation K (IsDiscreteValuationRing.maximalIdeal R₀) D'.yP ≤ 1 := by
    rw [← hxP, ← hyP]; exact ⟨valuation_le_one _ _, valuation_le_one _ _⟩
  have hvQ : valuation K (IsDiscreteValuationRing.maximalIdeal R₀) D'.xQ ≤ 1 ∧
      valuation K (IsDiscreteValuationRing.maximalIdeal R₀) D'.yQ ≤ 1 := by
    rw [← hxQ, ← hyQ]; exact ⟨valuation_le_one _ _, valuation_le_one _ _⟩
  obtain ⟨hP', hredP⟩ := WeierstrassCurve.reducePoint_some R₀ W hnsP hvP.1 hvP.2
  obtain ⟨hQ', hredQ⟩ := WeierstrassCurve.reducePoint_some R₀ W hnsQ hvQ.1 hvQ.2
  have hxPr : reduceCoord R₀ D'.xP = residue R₀ xP₀ := by rw [← hxP]; exact reduceCoord_algebraMap xP₀
  have hxQr : reduceCoord R₀ D'.xQ = residue R₀ xQ₀ := by rw [← hxQ]; exact reduceCoord_algebraMap xQ₀

  have key : ∀ {x₁ y₁ x₂ y₂ : K} (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
      (a₁ a₂ : R₀) (ha₁ : algebraMap R₀ K a₁ = x₁) (ha₂ : algebraMap R₀ K a₂ = x₂)
      (h₁' : (W.reduction R₀).toAffine.Nonsingular (reduceCoord R₀ x₁) (reduceCoord R₀ y₁))
      (h₂' : (W.reduction R₀).toAffine.Nonsingular (reduceCoord R₀ x₂) (reduceCoord R₀ y₂))
      (hr₁ : reducePoint_alt R₀ W (.some x₁ y₁ h₁) = .some _ _ h₁')
      (hr₂ : reducePoint_alt R₀ W (.some x₂ y₂ h₂) = .some _ _ h₂')
      (ht₁ : ℓ • WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ = 0)
      (ht₂ : ℓ • WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ = 0),
      IsUnit (ModularCurve.indepElt W ℓ x₁ x₂) → IsUnit (ModularCurve.indepElt W₀ ℓ a₁ a₂) := by
    intro x₁ y₁ x₂ y₂ h₁ h₂ a₁ a₂ ha₁ ha₂ h₁' h₂' hr₁ hr₂ ht₁ ht₂ hunitK
    by_contra hnu

    have hres0 : residue R₀ (ModularCurve.indepElt W₀ ℓ a₁ a₂) = 0 := by
      by_contra h; exact hnu ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp h)

    have hbar : ModularCurve.indepElt (W.reduction R₀) ℓ (reduceCoord R₀ x₁) (reduceCoord R₀ x₂) = 0 := by
      have e1 : reduceCoord R₀ x₁ = residue R₀ a₁ := by rw [← ha₁]; exact reduceCoord_algebraMap a₁
      have e2 : reduceCoord R₀ x₂ = residue R₀ a₂ := by rw [← ha₂]; exact reduceCoord_algebraMap a₂
      rw [hred, e1, e2, ModularCurve.indepElt_map, hres0]

    let φ := reduceHom' (R₀ := R₀) W
    have hφ : ∀ T, φ T = reducePoint_alt R₀ W T := fun _ => rfl
    have ht₁' : ℓ • (WeierstrassCurve.Affine.Point.some _ _ h₁' : (W.reduction R₀).toAffine.Point) = 0 := by
      rw [← hr₁, ← hφ, ← map_nsmul, ht₁, map_zero]

    obtain ⟨m, hm⟩ := (ModularCurve.indepElt_eq_zero_iff_mem_zmultiples hℓ2 h₁' h₂' ht₁').mp hbar

    have hdiff0 : reducePoint_alt R₀ W (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ - m • WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) = 0 := by
      rw [← hφ, map_sub, map_zsmul, hφ, hφ, hr₁, hr₂, ← hm, sub_self]
    have htor : ℓ • (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ - m • WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) = 0 := by
      rw [smul_sub, smul_comm, ht₁, ht₂, smul_zero, sub_zero]
    have heq := WeierstrassCurve.eq_zero_of_smul_eq_zero_of_reducePoint_eq_zero R₀ W hℓk _ htor hdiff0
    rw [sub_eq_zero] at heq
    have hmem : WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ ∈ AddSubgroup.zmultiples (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) :=
      ⟨m, heq.symm⟩
    have h0 := (ModularCurve.indepElt_eq_zero_iff_mem_zmultiples hℓ2 h₁ h₂ ht₁).mpr hmem
    exact hunitK.ne_zero h0
  exact
    { equation_P := heqP
      equation_Q := heqQ
      preΨ_P := hψP
      preΨ_Q := hψQ
      isUnit_indepElt_PQ := key hnsP hnsQ xP₀ xQ₀ hxP hxQ hP' hQ' hredP hredQ hℓP hℓQ hD'.isUnit_indepElt_PQ
      isUnit_indepElt_QP := key hnsQ hnsP xQ₀ xP₀ hxQ hxP hQ' hP' hredQ hredP hℓQ hℓP hD'.isUnit_indepElt_QP }

end S_ModularCurve_exists_map_eq_and_isLevelPStructure_of_isLevelPStructure_map
end P2MW
export P2MW.S_ModularCurve_exists_map_eq_and_isLevelPStructure_of_isLevelPStructure_map (solution)
