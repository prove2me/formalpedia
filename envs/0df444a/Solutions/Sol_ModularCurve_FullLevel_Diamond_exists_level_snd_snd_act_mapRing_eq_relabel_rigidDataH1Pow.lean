-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.exists_level_snd_snd_act_mapRing_eq_relabel_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/5ce673b3-d60f-5356-8e35-9ce61d900eb8

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

import Theorems.Thm_ModularCurve_FullLevel_Diamond_zsmul_toPoint_add_zsmul_toPoint_eq_toPoint_levelAut_of_map_eq_cuspData_rigidDataH1Pow
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_map_of_isSectionTransport
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_act_of_isSectionTransport
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_zlinComb_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_exists_level_snd_snd_act_mapRing_eq_relabel_rigidDataH1Pow
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

namespace H4Aux

theorem rawPair_eq {T : Type} [CommRing T] (W : WeierstrassCurve.Projective T) (z : RawDrinfeldPair T) (hz : z.curve = W)
    (P' Q' : Section W) (a b c d : T)
    (hP : IsSectionThrough z.P a b) (hQ : IsSectionThrough z.Q c d)
    (hP' : IsSectionThrough P' a b) (hQ' : IsSectionThrough Q' c d) :
    z = ⟨W, P', Q'⟩ := by
  obtain ⟨Wz, Pz, Qz⟩ := z
  dsimp only at hz hP hQ
  subst hz
  have e := (WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough Wz).2
  obtain rfl : Pz = P' := (e Pz P' a b a b hP hP').mpr ⟨rfl, rfl⟩
  obtain rfl : Qz = Q' := (e Qz Q' c d c d hQ hQ').mpr ⟨rfl, rfl⟩
  rfl

end H4Aux

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓA : IsUnit ((ℓg : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (C₀ : WeierstrassCurve.VariableChange (LaurentSeries L))
    (x : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw ↥K)
    (hx : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

      (((C₀.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2 + (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 ∧
        C₀.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C₀.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C₀.t = HahnSeries.C ((24 : L)⁻¹)) ∧

      x.curve.map (algebraMap ↥K (LaurentSeries L)) = C₀ • ModularCurve.tateBase L q ∧

      x.level.2.1.map (algebraMap ↥K (LaurentSeries L)) =
        (⟨(ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1,
          (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2,
          (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1,
          (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2⟩ :
            ModularCurve.LevelPData (LaurentSeries L)).variableChange C₀ ∧

      (∃ Px Py Qx Qy : ↥K,
        (Px : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C₀).xP ∧
        (Py : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C₀).yP ∧
        (Qx : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C₀).xQ ∧
        (Qy : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C₀).yQ ∧
        IsSectionThrough x.level.2.2.P Px Py ∧ IsSectionThrough x.level.2.2.Q Qx Qy) ∧

      (((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf (Quot.mk _ x) : ↥K) : LaurentSeries L) =
        ModularCurve.jqNModC L q)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L q (ξ ^ ℓg) q (q ^ 2 * M') H₁ γ⁻¹ K τ)

    (μ : (↥K)ˣ)
    (hμ : (((μ : (↥K)ˣ) : ↥K) : LaurentSeries L) * (2 * (ModularCurve.tateToricPoint L q (((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q) ^ ((γ 0 0 : ℤ)))).2 + (ModularCurve.tateToricPoint L q (((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q) ^ ((γ 0 0 : ℤ)))).1) * (2 * ((ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 + HahnSeries.C ((12 : L)⁻¹))) =
      (2 * (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2 + (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1) * (2 * ((ModularCurve.tateToricPoint L q (((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q) ^ ((γ 0 0 : ℤ)))).1 + HahnSeries.C ((12 : L)⁻¹))))
    (hc : ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)
            ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).curve = x.curve) :
    ∃ hΔ : IsUnit x.level.2.2.curve.Δ,
      ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)
            ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).level.2.2 =
        ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.2 hΔ := by

  haveI hN0 : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have h1z : ((1 : ZMod q)) ≠ 0 := one_ne_zero
  obtain ⟨Px, Py, Qx, Qy, hPx, hPy, hQx, hQy, hSP, hSQ⟩ := hx.2.2.2.1
  have hcurve : x.level.2.2.curve = x.curve := x.isLevel.1.2.2.1
  obtain ⟨hΔ, -⟩ := x.isLevel.1.2.2.2
  have hW : x.level.2.2.curve.map (algebraMap ↥K (LaurentSeries L)) = C₀ • ModularCurve.tateBase L q := by
    rw [hcurve]; exact hx.2.1
  have hD : (⟨Px, Py, Qx, Qy⟩ : ModularCurve.LevelPData ↥K).map (algebraMap ↥K (LaurentSeries L)) =
      (ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg)
        ![((1 : ZMod q) : ZMod q), 0] ![0, -((1 : ZMod q) : ZMod q)]).variableChange C₀ := by
    refine ModularCurve.LevelPData.ext hPx hPy ?_ ?_
    · exact hQx
    · exact hQy
  obtain ⟨⟨hns1, hns2⟩, h1, h2⟩ :=
    ModularCurve.FullLevel.Diamond.zsmul_toPoint_add_zsmul_toPoint_eq_toPoint_levelAut_of_map_eq_cuspData_rigidDataH1Pow
      q M' hqM' ℓg hℓg hℓg12 hℓgM' L ξ hξ hιξ H₁ hH₁ K hK γ hγ τ hτ C₀ hx.1 μ hμ x.level.2.2.curve hW (1 : ZMod q) h1z
      ⟨Px, Py, Qx, Qy⟩ hD
  refine ⟨hΔ, ?_⟩

  show (𝒯.act (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)
      (𝒯.map (((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A)) x.level.2.2)) = _

  obtain ⟨tP, tQ⟩ := WeierstrassCurve.DrinfeldGlobal.isSectionThrough_map_of_isSectionTransport A 𝒢 q 𝒯 h𝒯
    (((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A)) x.level.2.2 (hCO ↥K ↥K _ _) ⟨Px, Py, Qx, Qy⟩ hSP hSQ
  obtain ⟨uP, uQ⟩ := WeierstrassCurve.DrinfeldGlobal.isSectionThrough_act_of_isSectionTransport A 𝒢 q 𝒯 h𝒯
    (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K) (𝒯.map (((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A)) x.level.2.2)
    (hVC ↥K _ _) ⟨τ Px, τ Py, τ Qx, τ Qy⟩ tP tQ
  have exP : ((⟨τ Px, τ Py, τ Qx, τ Qy⟩ : ModularCurve.LevelPData ↥K).variableChange
      (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)).xP = ((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 2 * τ Px := by
    simp [ModularCurve.LevelPData.variableChange]
  have eyP : ((⟨τ Px, τ Py, τ Qx, τ Qy⟩ : ModularCurve.LevelPData ↥K).variableChange
      (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)).yP = ((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 3 * τ Py := by
    simp [ModularCurve.LevelPData.variableChange]
  have exQ : ((⟨τ Px, τ Py, τ Qx, τ Qy⟩ : ModularCurve.LevelPData ↥K).variableChange
      (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)).xQ = ((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 2 * τ Qx := by
    simp [ModularCurve.LevelPData.variableChange]
  have eyQ : ((⟨τ Px, τ Py, τ Qx, τ Qy⟩ : ModularCurve.LevelPData ↥K).variableChange
      (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)).yQ = ((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 3 * τ Qy := by
    simp [ModularCurve.LevelPData.variableChange]
  rw [exP, eyP] at uP
  rw [exQ, eyQ] at uQ

  have hz : (𝒯.act (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)
      (𝒯.map (((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A)) x.level.2.2)).curve = x.level.2.2.curve := by
    obtain ⟨hc1, -⟩ := h𝒯.1 ↥K (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)
      (𝒯.map (((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A)) x.level.2.2)
    obtain ⟨hc2, -⟩ := h𝒯.2 ↥K ↥K (((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A)) x.level.2.2
    rw [hc1, hc2, hcurve]
    exact hc

  obtain ⟨-, thrP⟩ := WeierstrassCurve.DrinfeldGlobal.isSectionThrough_zlinComb_of_isSectionThrough A 𝒢 h𝒢 h𝒢O
    x.level.2.2.curve hΔ x.level.2.2.P x.level.2.2.Q Px Py Qx Qy hSP hSQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0)
    ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
  obtain ⟨-, thrQ⟩ := WeierstrassCurve.DrinfeldGlobal.isSectionThrough_zlinComb_of_isSectionThrough A 𝒢 h𝒢 h𝒢O
    x.level.2.2.curve hΔ x.level.2.2.P x.level.2.2.Q Px Py Qx Qy hSP hSQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1)
    ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)
  have vP := thrP _ _ hns1 (h1.trans (dif_pos hns1))
  have vQ := thrQ _ _ hns2 (h2.trans (dif_pos hns2))
  exact H4Aux.rawPair_eq x.level.2.2.curve _ hz _ _ _ _ _ _ uP uQ vP vQ

end S_ModularCurve_FullLevel_Diamond_exists_level_snd_snd_act_mapRing_eq_relabel_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_exists_level_snd_snd_act_mapRing_eq_relabel_rigidDataH1Pow (solution)
