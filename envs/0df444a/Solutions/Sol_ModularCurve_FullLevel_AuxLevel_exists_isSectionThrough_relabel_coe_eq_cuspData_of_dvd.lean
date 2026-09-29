-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.exists_isSectionThrough_relabel_coe_eq_cuspData_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/14fd3c64-7dd2-5f77-9085-aa718a945a89

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_WeierstrassCurve_PointChart
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_zlinComb_of_isSectionThrough
import Theorems.Thm_ModularCurve_LevelRelabelling_relabel_tateBase_cuspData_eq_cuspData_zsmul_add_zsmul
import Theorems.Thm_ModularCurve_LevelRelabelling_relabel_smul_variableChange
import Theorems.Thm_ModularCurve_LevelRelabelling_relabel_map_eq_map_relabel
import Theorems.Thm_ModularCurve_LevelRelabelling_toPoint_relabel_eq_zsmul_add_zsmul
import Theorems.Thm_ModularCurve_isLevelPStructure_tateBase_cuspData_neg_of_dvd
import Theorems.Thm_ModularCurve_IsLevelPStructure_variableChange
import Theorems.Thm_ModularCurve_torsion_basis_of_map_eq_variableChange_tateBase_cuspData_of_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isSectionThrough_relabel_coe_eq_cuspData_of_dvd
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups Classical

namespace DCORE_node14

theorem torsion_basis_of_map_eq_variableChange_tateBase_cuspData_of_dvd
    (F : Type) [Field F] [CharZero F] (q : ℕ) [Fact q.Prime] (N : ℕ) [NeZero N] (m : ℕ) (hm : q * m = N)
    (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) N)
    (C : WeierstrassCurve.VariableChange (LaurentSeries F))
    (T : Type) [Field T] (φ : T →+* LaurentSeries F)
    (W : WeierstrassCurve T) (D : ModularCurve.LevelPData T)
    (hW : W.map φ = C • ModularCurve.tateBase F N)
    (hD : D.map φ = (ModularCurve.cuspData F N ζ ![(m : ZMod N), 0] ![0, -(m : ZMod N)]).variableChange C) :
    ∀ a b : ℤ,
      a • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP + b • ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ = 0 →
        (q : ℤ) ∣ a ∧ (q : ℤ) ∣ b := by
  obtain ⟨-, -, hqP, hqQ, h5⟩ :=
    ModularCurve.torsion_basis_of_map_eq_variableChange_tateBase_cuspData_of_mul_eq F q N m hm ζ hζ C T φ W D hW hD
  intro a b hab
  have hq0 : (0 : ℤ) < q := by exact_mod_cast (Fact.out : q.Prime).pos

  have hred : ∀ (c : ℤ) (X : W.toAffine.Point), (q : ℤ) • X = 0 → c • X = (c % q) • X := by
    intro c X hX
    calc c • X = ((q : ℤ) * (c / q) + c % q) • X := by rw [Int.mul_ediv_add_emod]
      _ = (c / q) • ((q : ℤ) • X) + (c % q) • X := by rw [add_zsmul, mul_comm, ← smul_smul]
      _ = (c % q) • X := by rw [hX, smul_zero, zero_add]
  have ha0 : 0 ≤ a % q := Int.emod_nonneg a hq0.ne'
  have hb0 : 0 ≤ b % q := Int.emod_nonneg b hq0.ne'
  have haq : a % q < q := Int.emod_lt_of_pos a hq0
  have hbq : b % q < q := Int.emod_lt_of_pos b hq0
  have h' : ((a % q).toNat : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP +
      ((b % q).toNat : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ = 0 := by
    rw [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0, ← hred a _ hqP, ← hred b _ hqQ]
    exact hab
  obtain ⟨ha, hb⟩ := h5 (a % q).toNat (b % q).toNat (by omega) (by omega) h'
  refine ⟨Int.dvd_of_emod_eq_zero (by omega), Int.dvd_of_emod_eq_zero (by omega)⟩

theorem toPoint_eq_some_of_ne_zero {T : Type} [Field T] (W : WeierstrassCurve T) (x y : T)
    (h : ModularCurve.LevelRelabelling.toPoint W x y ≠ 0) :
    ∃ hns : W.toAffine.Nonsingular x y, ModularCurve.LevelRelabelling.toPoint W x y = WeierstrassCurve.Affine.Point.some x y hns := by
  by_cases hns : W.toAffine.Nonsingular x y
  · exact ⟨hns, by rw [ModularCurve.LevelRelabelling.toPoint, dif_pos hns]⟩
  · exact absurd (by rw [ModularCurve.LevelRelabelling.toPoint, dif_neg hns]) h

end DCORE_node14

set_option maxHeartbeats 4000000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
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

    (C : WeierstrassCurve.VariableChange (LaurentSeries L)) (r : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw ↥K)
    (hr : haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩

      (((C.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 ∧
        C.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C.t = HahnSeries.C ((24 : L)⁻¹)) ∧

      r.curve.map (algebraMap ↥K (LaurentSeries L)) = C • ModularCurve.tateBase L (q * ℓ) ∧

      (∀ (p : ↥M'.primeFactors) (F' : Type) [Field F'] (f : L →+* F') (ζ : F'),
        IsPrimitiveRoot ζ ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        ((r.level.1 p).map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' (q * ℓ) (ζ ^ a)).1))) ∧

      r.level.2.1.map (algebraMap ↥K (LaurentSeries L)) = (ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(q : ZMod (q * ℓ)), 0] ![0, -(q : ZMod (q * ℓ))]).variableChange C ∧

      (∃ Px Py Qx Qy : ↥K,
        (Px : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).xP ∧
        (Py : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).yP ∧
        (Qx : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).xQ ∧
        (Qy : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).yQ ∧
        IsSectionThrough r.level.2.2.P Px Py ∧ IsSectionThrough r.level.2.2.Q Qx Qy))

    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (hγq : (q : ℤ) ∣ (γ 0 0 : ℤ))
    (hΔ : IsUnit r.level.2.2.curve.Δ) :
    haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
    ∃ a b a' b' : ↥K,
      IsSectionThrough (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) r.level.2.2 hΔ).P a b ∧
      IsSectionThrough (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) r.level.2.2 hΔ).Q a' b' ∧
      (a : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit
        ![0, -(((γ 1 0 : ℤ) : ZMod (q * ℓ)) * ℓ)] ![((γ 0 1 : ℤ) : ZMod (q * ℓ)) * ℓ, -(((γ 1 1 : ℤ) : ZMod (q * ℓ)) * ℓ)]).variableChange C).xP ∧
      (b : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit
        ![0, -(((γ 1 0 : ℤ) : ZMod (q * ℓ)) * ℓ)] ![((γ 0 1 : ℤ) : ZMod (q * ℓ)) * ℓ, -(((γ 1 1 : ℤ) : ZMod (q * ℓ)) * ℓ)]).variableChange C).yP := by
  haveI hN : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
  have hq0 : 0 < q := (Fact.out : q.Prime).pos
  obtain ⟨-, hcurve, -, -, Px, Py, Qx, Qy, hPx, hPy, hQx, hQy, hSP, hSQ⟩ := hr
  have hιinj : Function.Injective (algebraMap ↥K (LaurentSeries L)) := fun a b h => Subtype.ext h
  have hWc : r.level.2.2.curve = r.curve := r.isLevel.2.2.1
  have hWι : WeierstrassCurve.map (r.level.2.2.curve : WeierstrassCurve ↥K) (algebraMap ↥K (LaurentSeries L)) =
      (C • ModularCurve.tateBase L (q * ℓ)) := by
    rw [hWc]; exact hcurve
  have hDK : ((⟨Px, Py, Qx, Qy⟩ : ModularCurve.LevelPData ↥K)).map (algebraMap ↥K (LaurentSeries L)) = (ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C :=
    ModularCurve.LevelPData.ext hPx hPy hQx hQy

  have hdet : ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact h
  have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hγq' : (q : ℤ) ∣ ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := hγq
  have hγ10 : ¬ (q : ℤ) ∣ ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    intro h
    have : (q : ℤ) ∣ 1 := by
      rw [← hdet]; exact dvd_sub (dvd_mul_of_dvd_left hγq' _) (dvd_mul_of_dvd_right h _)
    exact hqp.not_dvd_one this
  have hγ01 : ¬ (q : ℤ) ∣ ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by
    intro h
    have : (q : ℤ) ∣ 1 := by
      rw [← hdet]; exact dvd_sub (dvd_mul_of_dvd_left hγq' _) (dvd_mul_of_dvd_left h _)
    exact hqp.not_dvd_one this

  have hindepK := DCORE_node14.torsion_basis_of_map_eq_variableChange_tateBase_cuspData_of_dvd L q (q * ℓ) ℓ rfl
    (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit hξ C ↥K (algebraMap ↥K (LaurentSeries L)) r.level.2.2.curve (⟨Px, Py, Qx, Qy⟩ : ModularCurve.LevelPData ↥K) hWι hDK
  have hindepL := DCORE_node14.torsion_basis_of_map_eq_variableChange_tateBase_cuspData_of_dvd L q (q * ℓ) ℓ rfl
    (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit hξ C (LaurentSeries L) (RingHom.id _) (C • ModularCurve.tateBase L (q * ℓ)) ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C)
    (by rw [WeierstrassCurve.map_id]) (by rw [ModularCurve.LevelPData.map_id])
  have hneK₁ := fun h => hγ10 (hindepK (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0) h).2
  have hneK₂ := fun h => hγ01 (hindepK (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 1) (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1) h).1
  have hneL₁ := fun h => hγ10 (hindepL (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0) h).2
  have hneL₂ := fun h => hγ01 (hindepL (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 1) (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1) h).1

  obtain ⟨Drel, hDreldef⟩ : ∃ Drel : ModularCurve.LevelPData ↥K,
      Drel = ModularCurve.LevelRelabelling.LevelPData.relabel r.level.2.2.curve ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) (⟨Px, Py, Qx, Qy⟩ : ModularCurve.LevelPData ↥K) := ⟨_, rfl⟩
  obtain ⟨hrelP, hrelQ⟩ := ModularCurve.LevelRelabelling.toPoint_relabel_eq_zsmul_add_zsmul r.level.2.2.curve ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) (⟨Px, Py, Qx, Qy⟩ : ModularCurve.LevelPData ↥K) hneK₁ hneK₂
  obtain ⟨hnsP, hsomeP⟩ := DCORE_node14.toPoint_eq_some_of_ne_zero r.level.2.2.curve Drel.xP Drel.yP
    (by rw [hDreldef, hrelP]; exact hneK₁)
  obtain ⟨hnsQ, hsomeQ⟩ := DCORE_node14.toPoint_eq_some_of_ne_zero r.level.2.2.curve Drel.xQ Drel.yQ
    (by rw [hDreldef, hrelQ]; exact hneK₂)
  have hzl := WeierstrassCurve.DrinfeldGlobal.isSectionThrough_zlinComb_of_isSectionThrough A 𝒢 h𝒢 h𝒢O r.level.2.2.curve hΔ
    r.level.2.2.P r.level.2.2.Q Px Py Qx Qy hSP hSQ
  have hIP : IsSectionThrough (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) r.level.2.2 hΔ).P Drel.xP Drel.yP :=
    (hzl (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0)).2 _ _ hnsP (by rw [← hsomeP, hDreldef, hrelP])
  have hIQ : IsSectionThrough (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) r.level.2.2 hΔ).Q Drel.xQ Drel.yQ :=
    (hzl (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 1) (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1)).2 _ _ hnsQ (by rw [← hsomeQ, hDreldef, hrelQ])

  haveI : (ModularCurve.tateBase L (q * ℓ)).IsElliptic := ⟨ModularCurve.isUnit_Δ_tateBase L (q * ℓ)⟩
  have hLPS : ModularCurve.IsLevelPStructure (ModularCurve.tateBase L (q * ℓ)) q (ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]) := by
    have hdiv : q * ℓ / q = ℓ := Nat.mul_div_cancel_left ℓ hq0
    have h := ModularCurve.isLevelPStructure_tateBase_cuspData_neg_of_dvd (R := L) (p := q)
      (by intro h; have := hq; omega) (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))
      (q * ℓ) (Dvd.intro ℓ rfl) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit (by
        rw [hdiv]
        have hζq : IsPrimitiveRoot (((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit : L) ^ ℓ) q :=
          hξ.pow (Nat.pos_of_ne_zero (NeZero.ne (q * ℓ))) (Nat.mul_comm q ℓ)
        exact hζq.geom_sum_eq_zero (Fact.out : q.Prime).one_lt)
    rwa [hdiv] at h
  have hLPSC := hLPS.variableChange C
  have hℓN : (ℓ : ZMod (q * ℓ)) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd (Fact.out : ℓ.Prime).pos h
    nlinarith [(Fact.out : ℓ.Prime).pos, hq]
  have hqℓint : ∀ c : ℤ, (((c : ℤ) : ZMod (q * ℓ)) * (ℓ : ZMod (q * ℓ)) = 0) ↔ (q : ℤ) ∣ c := by
    intro c
    rw [← Int.cast_natCast ℓ, ← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_mul]
    constructor
    · intro h
      exact Int.dvd_of_mul_dvd_mul_right (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero) h
    · intro h
      exact mul_dvd_mul_right h _
  have hv0 : (![(ℓ : ZMod (q * ℓ)), 0] : Fin 2 → ZMod (q * ℓ)) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
    exact hℓN this
  have hw0 : (![0, -(ℓ : ZMod (q * ℓ))] : Fin 2 → ZMod (q * ℓ)) ≠ 0 := by
    intro h
    have := congrFun h 1
    simp at this
    exact hℓN this
  have hv' : (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) • (![(ℓ : ZMod (q * ℓ)), 0] : Fin 2 → ZMod (q * ℓ)) + (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) • (![0, -(ℓ : ZMod (q * ℓ))] : Fin 2 → ZMod (q * ℓ)) = ![0, -(((γ 1 0 : ℤ) : ZMod (q * ℓ)) * ℓ)] := by
    ext i
    fin_cases i
    · simp [zsmul_eq_mul]
      exact (hqℓint _).2 hγq'
    · simp [zsmul_eq_mul]
  have hw' : (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) • (![(ℓ : ZMod (q * ℓ)), 0] : Fin 2 → ZMod (q * ℓ)) + (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) • (![0, -(ℓ : ZMod (q * ℓ))] : Fin 2 → ZMod (q * ℓ)) = ![((γ 0 1 : ℤ) : ZMod (q * ℓ)) * ℓ, -(((γ 1 1 : ℤ) : ZMod (q * ℓ)) * ℓ)] := by
    ext i
    fin_cases i
    · simp [zsmul_eq_mul]
    · simp [zsmul_eq_mul]
  have hv'0 : (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) • (![(ℓ : ZMod (q * ℓ)), 0] : Fin 2 → ZMod (q * ℓ)) + (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) • (![0, -(ℓ : ZMod (q * ℓ))] : Fin 2 → ZMod (q * ℓ)) ≠ 0 := by
    rw [hv']
    intro h
    have := congrFun h 1
    simp at this
    exact hγ10 ((hqℓint _).1 this)
  have hw'0 : (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) • (![(ℓ : ZMod (q * ℓ)), 0] : Fin 2 → ZMod (q * ℓ)) + (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) • (![0, -(ℓ : ZMod (q * ℓ))] : Fin 2 → ZMod (q * ℓ)) ≠ 0 := by
    rw [hw']
    intro h
    have := congrFun h 0
    simp at this
    exact hγ01 ((hqℓint _).1 this)
  have hTate := ModularCurve.LevelRelabelling.relabel_tateBase_cuspData_eq_cuspData_zsmul_add_zsmul L (q * ℓ) ξ hξ (![(ℓ : ZMod (q * ℓ)), 0] : Fin 2 → ZMod (q * ℓ)) (![0, -(ℓ : ZMod (q * ℓ))] : Fin 2 → ZMod (q * ℓ)) ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
    hv0 hw0 hv'0 hw'0
  have htwist : ModularCurve.LevelRelabelling.LevelPData.relabel (C • ModularCurve.tateBase L (q * ℓ)) ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C) =
      (ModularCurve.LevelRelabelling.LevelPData.relabel (ModularCurve.tateBase L (q * ℓ)) ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) (ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))])).variableChange C := by
    have h := ModularCurve.LevelRelabelling.relabel_smul_variableChange (C • ModularCurve.tateBase L (q * ℓ)) C⁻¹ ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
      ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C) hLPSC.equation_P hLPSC.equation_Q hneL₁ hneL₂
    rw [inv_smul_smul, ← ModularCurve.LevelPData.variableChange_mul, inv_mul_cancel,
      ModularCurve.LevelPData.variableChange_one] at h
    rw [h, ← ModularCurve.LevelPData.variableChange_mul, mul_inv_cancel, ModularCurve.LevelPData.variableChange_one]
  have hmap : Drel.map (algebraMap ↥K (LaurentSeries L)) = (ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit
      ![0, -(((γ 1 0 : ℤ) : ZMod (q * ℓ)) * ℓ)] ![((γ 0 1 : ℤ) : ZMod (q * ℓ)) * ℓ, -(((γ 1 1 : ℤ) : ZMod (q * ℓ)) * ℓ)]).variableChange C := by
    rw [hDreldef, ← ModularCurve.LevelRelabelling.relabel_map_eq_map_relabel (algebraMap ↥K (LaurentSeries L)) r.level.2.2.curve ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) (⟨Px, Py, Qx, Qy⟩ : ModularCurve.LevelPData ↥K), hWι, hDK, htwist, hTate,
      hv', hw']
  refine ⟨Drel.xP, Drel.yP, Drel.xQ, Drel.yQ, hIP, hIQ, ?_, ?_⟩
  · exact congrArg ModularCurve.LevelPData.xP hmap
  · exact congrArg ModularCurve.LevelPData.yP hmap

end S_ModularCurve_FullLevel_AuxLevel_exists_isSectionThrough_relabel_coe_eq_cuspData_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isSectionThrough_relabel_coe_eq_cuspData_of_dvd (solution)
