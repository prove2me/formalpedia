-- Prove2me | solution 1 for ModularCurve.LevelComponent.act_eq_of_mapRing_fstHom_eq_of_map_fstHom_eq_one_of_smul_curve_eq_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/57acbd82-eb6b-54c9-9502-fc67ec15f6db

import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_ModularCurve_IsGamma0PowAt_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
import Theorems.Thm_ModularCurve_IsGamma1Point_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelComponent_act_eq_of_mapRing_fstHom_eq_of_map_fstHom_eq_one_of_smul_curve_eq_rigidDataH1Pow
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Generic.isElliptic_curve ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing ModularCurve.LevelP.instCommRingVCRing ModularCurve.LevelP.instCommRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelPRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelQRingBorelPRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingVCPolyVCRing ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatUnivBasisRingXVCRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelPRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingVCRing ModularCurve.LevelP.instAlgebraVCPolyVCRing ModularCurve.LevelP.instAlgebraBorelPRingBorelRing ModularCurve.LevelP.instAwayBorelPRingBorelDenomBorelRing"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add ModularCurve.LevelP.VCRing.lift_vcVar ModularCurve.LevelP.BorelPRing.lift_xQ ModularCurve.LevelP.twoPointLift_xQ ModularCurve.LevelP.PsiRoot.lift_ofBase ModularCurve.LevelP.univVC_u ModularCurve.LevelP.twoPointLift_yP ModularCurve.LevelP.univVC_r ModularCurve.LevelP.TorsionPointRing.lift_torsionPtX ModularCurve.LevelP.TorsionPointRing.lift_ofPsiRoot ModularCurve.LevelP.TorsionPointRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_C ModularCurve.LevelP.BorelQRing.lift_of ModularCurve.LevelP.BorelPRing.lift_yQ ModularCurve.LevelP.BorelPRing.lift_ofUniv ModularCurve.LevelP.univVC_t ModularCurve.LevelP.BorelRing.lift_ofUniv ModularCurve.LevelP.univVC_s ModularCurve.LevelP.twoPointLift_xP ModularCurve.LevelP.twoPointLift_yQ ModularCurve.LevelP.TorsionPointRing.lift_torsionPtY ModularCurve.LevelP.BorelQRing.lift_borelQY ModularCurve.LevelP.VCRing.lift_algebraMap ModularCurve.LevelP.VCRing.lift_ofUniv ModularCurve.LevelP.PsiRoot.lift_psiRootX ModularCurve.LevelP.BorelRing.lift_algebraMap"
p2m_attr_erase "simp" "ModularCurve.LevelP.BorelPRing.lift_yP ModularCurve.LevelP.BasisRing.lift_ofTwoPoint ModularCurve.LevelP.BasisRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_X ModularCurve.LevelP.genericLift_X ModularCurve.LevelP.twoPointLift_ofBase ModularCurve.LevelP.BorelPRing.lift_xP"

set_option autoImplicit false
open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup AlgebraicGeometry CategoryTheory NeronModelInfra

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (ℓg M' : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) [NeZero M']
    (A₀ : Type) [CommRing A₀]
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (k : Type) [Field k] [Algebra A₀ k] (hℓk : ((ℓg : ℕ) : k) ≠ 0) (hM'k : ((M' : ℕ) : k) ≠ 0)
    (z z' : ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓg hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).Raw (DualNumber k))
    (hzz' : ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓg hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).mapRing ((TrivSqZeroExt.fstHom k k k).restrictScalars A₀) z =
      ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓg hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).mapRing ((TrivSqZeroExt.fstHom k k k).restrictScalars A₀) z')
    (C : WeierstrassCurve.VariableChange (DualNumber k))
    (hC : C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1) (hCz : C • z.curve = z'.curve) :
    ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓg hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).act C z = z' := by
  classical

  set π : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom with hπ
  have hπsurj : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, by rw [hπ]; rfl⟩
  have hπnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥ := by
    refine ⟨2, ?_⟩
    rw [show RingHom.ker π ^ 2 = RingHom.ker π * RingHom.ker π from pow_two _, eq_bot_iff, Ideal.mul_le]
    intro a ha b hb
    rw [RingHom.mem_ker] at ha hb
    change a.fst = 0 at ha
    change b.fst = 0 at hb
    rw [Ideal.mem_bot]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [TrivSqZeroExt.fst_mul, ha, hb, mul_zero, TrivSqZeroExt.fst_zero]
    · rw [TrivSqZeroExt.snd_mul, ha, hb, zero_smul, MulOpposite.op_zero, zero_smul, _root_.add_zero, TrivSqZeroExt.snd_zero]
  have hunit : ∀ m : ℕ, ((m : ℕ) : k) ≠ 0 → IsUnit ((m : ℕ) : DualNumber k) := by
    intro m hm
    have h := (isUnit_iff_ne_zero.mpr hm).map (algebraMap k (DualNumber k))
    rwa [map_natCast] at h

  have hcur : z.curve.map π = z'.curve.map π :=
    congrArg (fun w => ModularCurve.LevelComponent.Raw.curve w) hzz'
  have hlev := congrArg (fun w => ModularCurve.LevelComponent.Raw.level w) hzz'
  have hker0 : ∀ pf : ↥M'.primeFactors, (z.level.1 pf).map π = (z'.level.1 pf).map π := fun pf =>
    congr_fun (congrArg Prod.fst hlev) pf
  have hlevP0 : z.level.2.1.map π = z'.level.2.1.map π := congrArg (fun l => l.2.1) hlev

  have hΔ' : IsUnit z'.curve.Δ := z'.isUnit_Δ

  have hΓ₀ : ∀ pf : ↥M'.primeFactors,
      ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (pf : ℕ) (M'.factorization (pf : ℕ)))
        (z.level.1 pf) = z'.level.1 pf := by
    intro pf
    haveI : Fact (pf : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors pf.2⟩
    have hpunit : IsUnit (((pf : ℕ) : ℕ) : DualNumber k) := by
      refine hunit _ fun h0 => hM'k ?_
      obtain ⟨c, hc⟩ := Nat.dvd_of_mem_primeFactors pf.2
      rw [hc, Nat.cast_mul, h0, zero_mul]
    have h1 : ModularCurve.IsGamma0PowAt z'.curve (pf : ℕ) (M'.factorization (pf : ℕ))
        (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (pf : ℕ) (M'.factorization (pf : ℕ)))
          (z.level.1 pf)) := by
      rw [← hCz]; exact hM _ z.curve C _ _ _ (z.isLevel.1.1 pf)
    have h2 : ModularCurve.IsGamma0PowAt z'.curve (pf : ℕ) (M'.factorization (pf : ℕ)) (z'.level.1 pf) :=
      z'.isLevel.1.1 pf
    have hred : (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (pf : ℕ) (M'.factorization (pf : ℕ)))
        (z.level.1 pf)).map π = (z'.level.1 pf).map π := by
      rw [ModularCurve.kernelVariableChangeDeg_map, hC, ModularCurve.kernelVariableChangeDeg_one, hker0]
    obtain ⟨h, -, huniq⟩ := ModularCurve.IsGamma0PowAt.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
      π hπsurj hπnil z'.curve hΔ' (pf : ℕ) (M'.factorization (pf : ℕ)) hpunit ((z'.level.1 pf).map π)
      (ModularCurve.IsGamma0PowAt.map π _ _ _ h2)
    exact (huniq _ ⟨hred, h1⟩).trans (huniq _ ⟨rfl, h2⟩).symm

  have hΓℓ : z.level.2.1.variableChange C = z'.level.2.1 := by
    have hℓ3 : 3 ≤ ℓg := by omega
    have h1 : ModularCurve.IsGamma1Point z'.curve ℓg (z.level.2.1.variableChange C) := by
      rw [← hCz]; exact hℓ _ z.curve C _ z.isLevel.1.2.1
    have h2 : ModularCurve.IsGamma1Point z'.curve ℓg z'.level.2.1 := z'.isLevel.1.2.1
    have hred : (z.level.2.1.variableChange C).map π = z'.level.2.1.map π := by
      rw [ModularCurve.LevelPData.map_variableChange, hC, ModularCurve.LevelPData.variableChange_one, hlevP0]
    obtain ⟨D, -, huniq⟩ := ModularCurve.IsGamma1Point.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
      π hπsurj hπnil z'.curve hΔ' ℓg hℓg hℓ3 (hunit ℓg hℓk) (z'.level.2.1.map π) (h2.map π)
    exact (huniq _ ⟨hred, h1⟩).trans (huniq _ ⟨rfl, h2⟩).symm

  refine ModularCurve.LevelComponent.Raw.ext' hCz ?_
  exact Prod.ext (funext hΓ₀) (Prod.ext hΓℓ rfl)

end S_ModularCurve_LevelComponent_act_eq_of_mapRing_fstHom_eq_of_map_fstHom_eq_one_of_smul_curve_eq_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_LevelComponent_act_eq_of_mapRing_fstHom_eq_of_map_fstHom_eq_one_of_smul_curve_eq_rigidDataH1Pow (solution)
