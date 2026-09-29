-- Prove2me | solution 1 for ModularCurve.LevelP.isReduced_univBasisRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/f593ef6f-dfdf-5d28-ac49-38266f40fa2e

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Theorems.Thm_ModularCurve_LevelP_BasisRing_etale
import Theorems.Thm_ModularCurve_LevelP_BasisRing_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelP_isReduced_univBasisRing
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

open scoped TensorProduct

namespace KatzRelabelRED

open ModularCurve ModularCurve.LevelP WeierstrassCurve

theorem pDelta_ne_zero (ℓ : ℕ) (hℓ : ℓ ≠ 0) : pDelta ℓ ≠ 0 := by
  intro h

  have h1 := congrArg (MvPolynomial.eval (![0, 0, 0, -1, 0] : Fin 5 → ℤ)) h
  rw [pDelta, map_mul, map_natCast, ← WeierstrassCurve.map_Δ, map_zero] at h1
  have h2 : (genericCurve.map (MvPolynomial.eval (![0, 0, 0, -1, 0] : Fin 5 → ℤ))) =
      (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℤ) := by
    simp [genericCurve, WeierstrassCurve.map]
  rw [h2] at h1
  have h3 : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℤ).Δ = 64 := by
    simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
  rw [h3] at h1
  have : (ℓ : ℤ) * 64 ≠ 0 := mul_ne_zero (by exact_mod_cast hℓ) (by norm_num)
  exact this h1

scoped instance isDomain_univBase (ℓ : ℕ) [Fact ℓ.Prime] : IsDomain (UnivBase ℓ) :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (pDelta_ne_zero ℓ (Fact.out : ℓ.Prime).ne_zero))

theorem isReduced (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) : IsReduced (UnivBasisRing ℓ) := by
  have hodd : Odd ℓ := (Fact.out : ℓ.Prime).odd_of_ne_two hℓ2
  haveI hflat : Module.Flat (UnivBase ℓ) (UnivBasisRing ℓ) :=
    ModularCurve.LevelP.BasisRing.flat (univCurve ℓ) ℓ hodd (Fact.out : ℓ.Prime).one_lt.ne'
      (isUnit_natCast_univBase ℓ)
  haveI hetale : Algebra.Etale (UnivBase ℓ) (UnivBasisRing ℓ) :=
    ModularCurve.LevelP.BasisRing.etale (univCurve ℓ) hodd (isUnit_natCast_mul_Δ_univCurve ℓ)
  let K := FractionRing (UnivBase ℓ)
  let A := K ⊗[UnivBase ℓ] UnivBasisRing ℓ
  haveI : Algebra.Etale K A := inferInstance
  haveI : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field K A
  let f : UnivBasisRing ℓ →ₐ[UnivBase ℓ] A := Algebra.TensorProduct.includeRight
  have hf : Function.Injective f := by
    have : ⇑f = (LinearMap.rTensor (UnivBasisRing ℓ)
        (Algebra.ofId (UnivBase ℓ) K).toLinearMap).comp
        (Algebra.TensorProduct.lid (UnivBase ℓ) (UnivBasisRing ℓ)).symm.toLinearMap := by
      ext x; simp [f, A]
    rw [this, LinearMap.coe_comp]
    refine Function.Injective.comp ?_ (Algebra.TensorProduct.lid (UnivBase ℓ) (UnivBasisRing ℓ)).symm.injective
    exact Module.Flat.rTensor_preserves_injective_linearMap (Algebra.ofId (UnivBase ℓ) K).toLinearMap
      (fun a b h => IsFractionRing.injective (UnivBase ℓ) K h)
  exact isReduced_of_injective f hf

end KatzRelabelRED
p2m_reactivate "P2MW.S_ModularCurve_LevelP_isReduced_univBasisRing.KatzRelabelRED"

theorem solution (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) :
    IsReduced (ModularCurve.LevelP.UnivBasisRing ℓ) :=
  KatzRelabelRED.isReduced ℓ hℓ2

end S_ModularCurve_LevelP_isReduced_univBasisRing
end P2MW
export P2MW.S_ModularCurve_LevelP_isReduced_univBasisRing (solution)
