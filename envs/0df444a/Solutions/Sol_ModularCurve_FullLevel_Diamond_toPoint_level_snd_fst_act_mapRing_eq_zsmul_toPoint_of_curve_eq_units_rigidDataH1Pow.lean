-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.toPoint_level_snd_fst_act_mapRing_eq_zsmul_toPoint_of_curve_eq_units_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/786faf61-3d6a-5a56-a72d-20bf10842f4a

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

import Theorems.Thm_ModularCurve_FullLevel_Diamond_toPoint_levelAut_eq_zsmul_toPoint_of_map_eq_tateToricPoint_rigidDataH1Pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_toPoint_level_snd_fst_act_mapRing_eq_zsmul_toPoint_of_curve_eq_units_rigidDataH1Pow
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

set_option maxHeartbeats 4000000 in
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
    [DecidableEq ↥K]
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
    ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange ↥K)
        ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)
            ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).level.2.1.xP
        ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)
            ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).level.2.1.yP =
      (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) •
        ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange ↥K) x.level.2.1.xP x.level.2.1.yP ∧
    ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)
            ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).level.2.1.xQ =
      ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)
            ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).level.2.1.xP ∧
    ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)
            ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).level.2.1.yQ =
      ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)
            ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).level.2.1.yP := by
  haveI hN0 : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hG1 : ModularCurve.IsGamma1Point x.curve ℓg x.level.2.1 := x.isLevel.1.2.1
  obtain ⟨hP, h1⟩ :=
    ModularCurve.FullLevel.Diamond.toPoint_levelAut_eq_zsmul_toPoint_of_map_eq_tateToricPoint_rigidDataH1Pow
      q M' hqM' ℓg hℓg hℓg12 hℓgM' L ξ hξ hιξ H₁ hH₁ K hK γ hγ τ hτ C₀ hx.1 μ hμ x.curve hx.2.1 x.level.2.1 hx.2.2.1
  have hbc : (x.curve).baseChange ↥K = x.curve := by
    rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
  have exP : ((x.level.2.1.map (((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A).toRingHom)).variableChange
      (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)).xP = ((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 2 * τ x.level.2.1.xP := by
    simp [ModularCurve.LevelPData.variableChange, ModularCurve.LevelPData.map]
  have eyP : ((x.level.2.1.map (((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A).toRingHom)).variableChange
      (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)).yP = ((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 3 * τ x.level.2.1.yP := by
    simp [ModularCurve.LevelPData.variableChange, ModularCurve.LevelPData.map]
  have exQ : ((x.level.2.1.map (((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A).toRingHom)).variableChange
      (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)).xQ = ((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 2 * τ x.level.2.1.xQ := by
    simp [ModularCurve.LevelPData.variableChange, ModularCurve.LevelPData.map]
  have eyQ : ((x.level.2.1.map (((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A).toRingHom)).variableChange
      (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)).yQ = ((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 3 * τ x.level.2.1.yQ := by
    simp [ModularCurve.LevelPData.variableChange, ModularCurve.LevelPData.map]

  show ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange ↥K) ((x.level.2.1.map (((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A).toRingHom)).variableChange
        (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)).xP ((x.level.2.1.map (((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A).toRingHom)).variableChange
        (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)).yP =
      (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) •
        ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange ↥K) x.level.2.1.xP x.level.2.1.yP ∧
    ((x.level.2.1.map (((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A).toRingHom)).variableChange
        (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)).xQ = ((x.level.2.1.map (((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A).toRingHom)).variableChange
        (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)).xP ∧ ((x.level.2.1.map (((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A).toRingHom)).variableChange
        (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)).yQ = ((x.level.2.1.map (((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A).toRingHom)).variableChange
        (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)).yP
  rw [exP, eyP, exQ, eyQ, hbc, hG1.xQ_eq, hG1.yQ_eq]
  exact ⟨h1, rfl, rfl⟩

end S_ModularCurve_FullLevel_Diamond_toPoint_level_snd_fst_act_mapRing_eq_zsmul_toPoint_of_curve_eq_units_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_toPoint_level_snd_fst_act_mapRing_eq_zsmul_toPoint_of_curve_eq_units_rigidDataH1Pow (solution)
