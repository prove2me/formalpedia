-- Prove2me | solution 1 for ModularCurve.FullLevel.map_eq_one_or_eq_neg_one_of_act_eq_self_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/01d67002-b542-52f6-9cc4-351c686eb8f6

import Mathlib
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
import Theorems.Thm_ModularCurve_IsLevelPStructure_relabel_of_isUnit_det
import Theorems.Thm_ModularCurve_IsLevelPStructure_map_eq_of_relabel_variableChange_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_map_eq_of_act_relabel_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_zlinComb_zlinComb_of_isUnit_det
import Theorems.Thm_WeierstrassProjModel_mul_comm_of_isPointsEval
import Theorems.Thm_WeierstrassCurve_variableChange_smul_eq_self_iff_of_c4_ne_zero_of_c6_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_map_eq_one_or_eq_neg_one_of_act_eq_self_gamma0Pow
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X"

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_FullLevel_map_eq_one_or_eq_neg_one_of_act_eq_self_gamma0Pow.ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel"

open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC jqModC_rat map_jqModC qExpand qExpand_coeff_mul jq coeff_jq_neg_one coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange FullLevel.levelH xHFunctionField RigidWeierstrassData RigidWeierstrassData.Rel RigidWeierstrassData.Rel.refl RigidWeierstrassData.Rel.trans kernelVariableChangeDeg LevelPData IsLevelPStructure gamma0PowDeg IsGamma0PowAt LevelRelabelling.LevelPData.relabel LevelRelabelling.RawDrinfeldPair.relabel IsLevelPStructure.relabel_of_isUnit_det IsLevelPStructure.map_eq_of_relabel_variableChange_eq"
namespace FixedByRelabellingAssembly
p2m_open "ModularCurve"

theorem rel_equivalence {A : Type} [CommRing A] (R : RigidWeierstrassData A) (T : Type) [CommRing T] [Algebra A T] :
    Equivalence (R.Rel (T := T)) where
  refl x := RigidWeierstrassData.Rel.refl R x
  symm := by
    rintro x y ⟨C, rfl⟩
    exact ⟨C⁻¹, by rw [← R.act_mul, inv_mul_cancel, R.act_one]⟩
  trans := fun h h' => RigidWeierstrassData.Rel.trans R h h'

theorem matrix_map_eq_of_coprime {n : Type*} [Fintype n] [DecidableEq n] (q ℓ : ℕ) (hcop : q.Coprime ℓ)
    (g h : Matrix n n ℤ)
    (hq : g.map (Int.castRingHom (ZMod q)) = h.map (Int.castRingHom (ZMod q)))
    (hℓ : g.map (Int.castRingHom (ZMod ℓ)) = h.map (Int.castRingHom (ZMod ℓ))) :
    g.map (Int.castRingHom (ZMod (q * ℓ))) = h.map (Int.castRingHom (ZMod (q * ℓ))) := by
  ext i j
  have hq' := congrFun (congrFun hq i) j
  have hℓ' := congrFun (congrFun hℓ i) j
  simp only [Matrix.map_apply, Int.coe_castRingHom] at hq' hℓ' ⊢
  rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd] at hq' hℓ' ⊢
  push_cast
  exact (Nat.Coprime.isCoprime hcop).mul_dvd hq' hℓ'

theorem coeff_jqNModC_neg (L : Type) [Field L] [CharZero L] (N : ℕ) [NeZero N] :
    (jqNModC L N).coeff (-(N : ℤ)) = 1 := by
  have h1 : (jqModC L).coeff (-1) = 1 := by
    have : jqModC L = coeffMap (algebraMap ℚ L) jq := by
      rw [← jqModC_rat]; exact (map_jqModC (algebraMap ℚ L)).symm
    rw [this, coeffMap_coeff, coeff_jq_neg_one, map_one]
  rw [show (-(N : ℤ)) = (N : ℤ) * (-1) by ring]
  show (qExpand L N (jqModC L)).coeff ((N : ℤ) * (-1)) = 1
  rw [qExpand_coeff_mul, h1]

end ModularCurve.FixedByRelabellingAssembly

open ModularCurve.FixedByRelabellingAssembly in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
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
    (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx : (((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) =
      ModularCurve.jqNModC L (q * ℓ))
    (ρ : ↥(CongruenceSubgroup.Gamma0 M') → (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut)

    (hρ : ∀ (γ : ↥(CongruenceSubgroup.Gamma0 M')) (T : Type) [Field T] [Algebra A T]
      (x x' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ),
      x'.curve = x.curve →
      x'.level.1 = x.level.1 →
      x'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel x.curve
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.1 →
      x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.2 hΔ →
      (ρ γ).act (Quot.mk _ x) = Quot.mk _ x')
    (γ : ↥(CongruenceSubgroup.Gamma0 M')) (hfix : (ρ γ).act x = x) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (q * ℓ))) (γ : SL(2, ℤ)) = 1 ∨
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (q * ℓ))) (γ : SL(2, ℤ)) = -1 := by
  classical
  obtain ⟨x0, rfl⟩ := Quot.exists_rep x
  have hqP : q.Prime := Fact.out
  have hℓP : ℓ.Prime := Fact.out
  haveI : CharZero ↥K := charZero_of_injective_algebraMap (algebraMap L ↥K).injective
  haveI hqlz : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero hqP.ne_zero hℓP.ne_zero⟩
  have hℓK : ((ℓ : ℕ) : ↥K) ≠ 0 := Nat.cast_ne_zero.mpr hℓP.ne_zero
  have hqK : ((q : ℕ) : ↥K) ≠ 0 := Nat.cast_ne_zero.mpr hqP.ne_zero
  set g : Matrix (Fin 2) (Fin 2) ℤ := ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hg
  have hdet : g.det = 1 := (γ : SL(2, ℤ)).prop
  have hdetℓ : IsUnit ((g.det : ℤ) : ZMod ℓ) := by rw [hdet, Int.cast_one]; exact isUnit_one
  have hdetq : IsUnit ((g.det : ℤ) : ZMod q) := by rw [hdet, Int.cast_one]; exact isUnit_one

  have hD : IsLevelPStructure x0.curve ℓ x0.level.2.1 := x0.isLevel.2.1
  have hPQ : RawDrinfeldPair.IsLevel 𝒢 q x0.curve x0.level.2.2 := x0.isLevel.2.2
  have hcurvePQ : x0.level.2.2.curve = x0.curve := hPQ.1
  have hΔPQ : IsUnit x0.level.2.2.curve.Δ := by rw [hcurvePQ]; exact x0.isUnit_Δ

  have hD' : IsLevelPStructure x0.curve ℓ (LevelRelabelling.LevelPData.relabel x0.curve g x0.level.2.1) :=
    ModularCurve.IsLevelPStructure.relabel_of_isUnit_det ℓ hℓ3 hℓK x0.curve x0.isUnit_Δ x0.level.2.1 hD g hdetℓ
  obtain ⟨ev, hev⟩ := h𝒢 (↥K) x0.level.2.2.curve hΔPQ
  haveI : WeierstrassCurve.IsElliptic (x0.level.2.2.curve : WeierstrassCurve ↥K) := ⟨hΔPQ⟩
  have hcomm : ∀ a b : Section x0.level.2.2.curve,
      (𝒢 (↥K) x0.level.2.2.curve hΔPQ).mul _ a b = (𝒢 (↥K) x0.level.2.2.curve hΔPQ).mul _ b a :=
    fun a b => WeierstrassProjModel.mul_comm_of_isPointsEval (↥K) x0.level.2.2.curve
      (𝒢 (↥K) x0.level.2.2.curve hΔPQ) ev hev (𝟙 _) a b
  obtain ⟨hΔ0, hbasis⟩ := hPQ.2
  have hbasis' := WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.zlinComb_zlinComb_of_isUnit_det
    (𝒢 (↥K) x0.level.2.2.curve hΔPQ) hcomm q x0.level.2.2.P x0.level.2.2.Q hbasis g hdetq
  have hPQ' : RawDrinfeldPair.IsLevel 𝒢 q x0.curve
      (LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x0.level.2.2 hΔPQ) :=
    ⟨hcurvePQ, hΔPQ, hbasis'⟩

  let x1 : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw ↥K :=
    ⟨x0.curve, x0.isUnit_Δ,
      (x0.level.1, (LevelRelabelling.LevelPData.relabel x0.curve g x0.level.2.1,
        LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x0.level.2.2 hΔPQ)),
      ⟨x0.isLevel.1, hD', hPQ'⟩⟩
  have hpin : (ρ γ).act (Quot.mk _ x0) = Quot.mk _ x1 := hρ γ (↥K) x0 x1 hΔPQ rfl rfl rfl rfl
  have heq : Quot.mk _ x1 = Quot.mk _ x0 := hpin.symm.trans hfix
  obtain ⟨C, hC⟩ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Rel x1 x0 :=
    ((rel_equivalence _ (↥K)).eqvGen_iff).mp (Quot.eq.mp heq)
  have hCE : C • x0.curve = x0.curve :=
    (congrArg (fun z : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw ↥K => z.curve) hC).symm
  have hCD : (LevelRelabelling.LevelPData.relabel x0.curve g x0.level.2.1).variableChange C = x0.level.2.1 :=
    (congrArg (fun z : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw ↥K => z.level.2.1) hC).symm
  have hCPQ : 𝒯.act C (LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x0.level.2.2 hΔPQ) = x0.level.2.2 :=
    (congrArg (fun z : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw ↥K => z.level.2.2) hC).symm

  haveI hE : x0.curve.IsElliptic := ⟨x0.isUnit_Δ⟩
  have hjE : ((x0.curve.j : ↥K) : LaurentSeries L) = jqNModC L (q * ℓ) := by
    rw [← WeierstrassCurve.jOfUnit_eq_j _ x0.isUnit_Δ]; exact hx
  have hpole := coeff_jqNModC_neg L (q * ℓ)
  have hc4 : x0.curve.c₄ ≠ 0 := by
    intro h0
    have hj0 : x0.curve.j = 0 := by rw [WeierstrassCurve.j, h0]; ring
    rw [hj0] at hjE
    have := congrArg (fun z : LaurentSeries L => z.coeff (-((q * ℓ : ℕ) : ℤ))) hjE
    simp only [hpole] at this
    have h01 : (0 : L) = 1 := by simpa using this
    exact zero_ne_one h01
  have hc6 : x0.curve.c₆ ≠ 0 := by
    intro h0
    have hrel := x0.curve.c_relation
    rw [h0, zero_pow two_ne_zero, sub_zero] at hrel
    have hj0 : x0.curve.j = 1728 := by
      rw [WeierstrassCurve.j, ← hrel, ← WeierstrassCurve.coe_Δ', mul_left_comm, Units.inv_mul, mul_one]
    rw [hj0] at hjE
    have := congrArg (fun z : LaurentSeries L => z.coeff (-((q * ℓ : ℕ) : ℤ))) hjE
    simp only [hpole] at this
    have h1728 : (((1728 : ↥K) : LaurentSeries L)) = algebraMap L (LaurentSeries L) 1728 := by
      rw [map_ofNat]; exact map_ofNat K.val.toRingHom 1728
    rw [h1728, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne] at this
    · exact zero_ne_one this
    · rw [ne_eq, neg_eq_zero, Nat.cast_eq_zero]; exact NeZero.ne (q * ℓ)
  have h2 : (2 : ↥K) ≠ 0 := two_ne_zero
  have h3 : (3 : ↥K) ≠ 0 := three_ne_zero
  have hCiff := (WeierstrassCurve.variableChange_smul_eq_self_iff_of_c4_ne_zero_of_c6_ne_zero h2 h3 x0.curve hc4 hc6 C).mp hCE

  have hK := ModularCurve.IsLevelPStructure.map_eq_of_relabel_variableChange_eq ℓ hℓ3 hℓK x0.curve x0.isUnit_Δ
    x0.level.2.1 hD g hdetℓ C hCD
  have hQ := WeierstrassCurve.DrinfeldGlobal.map_eq_of_act_relabel_eq 𝒢 h𝒢 h𝒢O q 𝒯 h𝒯 hVC (↥K) hqK x0.curve
    x0.level.2.2 hΔPQ hPQ g C hCPQ

  have hcop : q.Coprime ℓ := (Nat.coprime_primes hqP hℓP).mpr (Ne.symm hℓq)
  rcases hCiff with rfl | rfl
  · left
    have h' := matrix_map_eq_of_coprime q ℓ hcop g 1
      (by rw [hQ.1 rfl, Matrix.map_one _ (map_zero _) (map_one _)])
      (by rw [hK.1 rfl, Matrix.map_one _ (map_zero _) (map_one _)])
    apply Subtype.ext
    show g.map (Int.castRingHom (ZMod (q * ℓ))) = ((1 : SL(2, ZMod (q * ℓ))) : Matrix (Fin 2) (Fin 2) (ZMod (q * ℓ)))
    rw [h', Matrix.map_one _ (map_zero _) (map_one _), Matrix.SpecialLinearGroup.coe_one]
  · right
    have hm1 : ∀ (m : ℕ), (-1 : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod m)) = -1 := fun m => by
      show (Int.castRingHom (ZMod m)).mapMatrix (-1) = -1
      rw [map_neg, map_one]
    have h' := matrix_map_eq_of_coprime q ℓ hcop g (-1)
      (by rw [hQ.2 (by rw [hcurvePQ]), hm1])
      (by rw [hK.2 rfl, hm1])
    apply Subtype.ext
    show g.map (Int.castRingHom (ZMod (q * ℓ))) = ((-1 : SL(2, ZMod (q * ℓ))) : Matrix (Fin 2) (Fin 2) (ZMod (q * ℓ)))
    rw [h', hm1, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]

end S_ModularCurve_FullLevel_map_eq_one_or_eq_neg_one_of_act_eq_self_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_map_eq_one_or_eq_neg_one_of_act_eq_self_gamma0Pow (solution)
