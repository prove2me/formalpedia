-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_trivial_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/f869ee39-46fe-5cb9-b5bf-e76cf615814f

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Theorems.Thm_ModularCurve_IsGamma0PowAt_existsUnique_tuple_map_eq_of_surjective_of_ker_pow_eq_bot
import Theorems.Thm_ModularCurve_IsGamma1Point_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
import Theorems.Thm_ModularCurve_IsGamma1Link_of_map_of_surjective_of_ker_pow_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_trivial_rigidDataH1Pow
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Generic.isElliptic_curve ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing ModularCurve.LevelP.instCommRingVCRing ModularCurve.LevelP.instCommRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelPRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelQRingBorelPRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingVCPolyVCRing ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatUnivBasisRingXVCRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelPRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingVCRing ModularCurve.LevelP.instAlgebraVCPolyVCRing ModularCurve.LevelP.instAlgebraBorelPRingBorelRing ModularCurve.LevelP.instAwayBorelPRingBorelDenomBorelRing"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add ModularCurve.LevelP.VCRing.lift_vcVar ModularCurve.LevelP.BorelPRing.lift_xQ ModularCurve.LevelP.twoPointLift_xQ ModularCurve.LevelP.PsiRoot.lift_ofBase ModularCurve.LevelP.univVC_u ModularCurve.LevelP.twoPointLift_yP ModularCurve.LevelP.univVC_r ModularCurve.LevelP.TorsionPointRing.lift_torsionPtX ModularCurve.LevelP.TorsionPointRing.lift_ofPsiRoot ModularCurve.LevelP.TorsionPointRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_C ModularCurve.LevelP.BorelQRing.lift_of ModularCurve.LevelP.BorelPRing.lift_yQ ModularCurve.LevelP.BorelPRing.lift_ofUniv ModularCurve.LevelP.univVC_t ModularCurve.LevelP.BorelRing.lift_ofUniv ModularCurve.LevelP.univVC_s ModularCurve.LevelP.twoPointLift_xP ModularCurve.LevelP.twoPointLift_yQ ModularCurve.LevelP.TorsionPointRing.lift_torsionPtY ModularCurve.LevelP.BorelQRing.lift_borelQY ModularCurve.LevelP.VCRing.lift_algebraMap ModularCurve.LevelP.VCRing.lift_ofUniv ModularCurve.LevelP.PsiRoot.lift_psiRootX ModularCurve.LevelP.BorelRing.lift_algebraMap"
p2m_attr_erase "simp" "ModularCurve.LevelP.BorelPRing.lift_yP ModularCurve.LevelP.BasisRing.lift_ofTwoPoint ModularCurve.LevelP.BasisRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_X ModularCurve.LevelP.genericLift_X ModularCurve.LevelP.twoPointLift_ofBase ModularCurve.LevelP.BorelPRing.lift_xP WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

open ModularCurve

theorem solution
    (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) [NeZero M']
    (A₀ : Type) [CommRing A₀]
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
        ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓ n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    {B T : Type} [CommRing B] [CommRing T] [Algebra A₀ B] [Algebra A₀ T]
    (π : B →ₐ[A₀] T) (hπ : Function.Surjective π) (hnil : ∃ n : ℕ, RingHom.ker π.toRingHom ^ n = ⊥)
    (hℓT : IsUnit ((ℓ : ℕ) : T)) (hM'T : IsUnit ((M' : ℕ) : T)) :
    Function.Surjective (((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum.map π) := by
  classical
  obtain ⟨n, hn⟩ := hnil
  set R := ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid) with hR

  have hlift : ∀ b : B, IsUnit (π b) → IsUnit b := by
    intro b hb
    obtain ⟨c, hc⟩ := hπ (hb.unit⁻¹ : Tˣ)
    have hbc : π (b * c) = 1 := by rw [map_mul, hc]; exact hb.mul_val_inv
    have hk : b * c - 1 ∈ RingHom.ker π.toRingHom := by
      rw [RingHom.mem_ker]; simp [map_sub, hbc]
    have hnilp : IsNilpotent (b * c - 1) := ⟨n, by
      have := Ideal.pow_mem_pow hk n
      rwa [hn, Ideal.mem_bot] at this⟩
    have hu : IsUnit (b * c) := by
      have := hnilp.isUnit_add_one
      rwa [sub_add_cancel] at this
    exact isUnit_of_mul_isUnit_left hu
  have hℓB : IsUnit ((ℓ : ℕ) : B) := hlift _ (by rwa [map_natCast])
  have hM'B : IsUnit ((M' : ℕ) : B) := hlift _ (by rwa [map_natCast])
  have hℓ3 : 3 ≤ ℓ := by omega

  intro y
  obtain ⟨x, rfl⟩ := Quot.exists_rep y
  obtain ⟨W, hΔ, ⟨h, D, u⟩, ⟨⟨hh, hD, -⟩, hlk⟩⟩ := x

  obtain ⟨b₁, hb₁⟩ := hπ W.a₁
  obtain ⟨b₂, hb₂⟩ := hπ W.a₂
  obtain ⟨b₃, hb₃⟩ := hπ W.a₃
  obtain ⟨b₄, hb₄⟩ := hπ W.a₄
  obtain ⟨b₆, hb₆⟩ := hπ W.a₆
  let WB : WeierstrassCurve B := ⟨b₁, b₂, b₃, b₄, b₆⟩
  have hWB : WB.map π.toRingHom = W := by
    ext <;> simp [WB, WeierstrassCurve.map, hb₁, hb₂, hb₃, hb₄, hb₆]
  have hΔB : IsUnit WB.Δ := by
    apply hlift
    have : π.toRingHom WB.Δ = (WB.map π.toRingHom).Δ := (WB.map_Δ π.toRingHom).symm
    rw [hWB] at this
    exact this ▸ hΔ

  obtain ⟨hB, ⟨hhBmap, hhB⟩, -⟩ :=
    ModularCurve.IsGamma0PowAt.existsUnique_tuple_map_eq_of_surjective_of_ker_pow_eq_bot π.toRingHom hπ ⟨n, hn⟩
      WB hΔB M' hM'B h (by rw [hWB]; exact hh)
  obtain ⟨DB, ⟨hDBmap, hDB⟩, -⟩ :=
    ModularCurve.IsGamma1Point.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot π.toRingHom hπ ⟨n, hn⟩
      WB hΔB ℓ Fact.out hℓ3 hℓB D (by rw [hWB]; exact hD)
  have hlkB : ModularCurve.IsGamma1Link WB ℓ M' hB DB :=
    ModularCurve.IsGamma1Link.of_map_of_surjective_of_ker_pow_eq_bot π.toRingHom hπ ⟨n, hn⟩ WB hΔB ℓ Fact.out hℓ3 hℓB
      M' hM'B hB hhB DB hDB (by rw [hWB, hDBmap]; exact (funext fun p => congrFun hhBmap p) ▸ hlk)
  let xB : R.Raw B := ⟨WB, hΔB, ⟨hB, DB, u⟩, ⟨⟨hhB, hDB, trivial⟩, hlkB⟩⟩
  refine ⟨Quot.mk _ xB, ?_⟩
  show R.map π (Quot.mk _ xB) = Quot.mk _ _
  rw [ModularCurve.RigidWeierstrassData.map_mk]
  congr 1
  apply ModularCurve.LevelComponent.Raw.ext'
  · exact hWB
  · show ((fun p => (hB p).map π.toRingHom), (DB.map π.toRingHom, u)) = (h, (D, u))
    rw [hhBmap, hDBmap]
    rfl

end S_ModularCurve_FullLevel_Diamond_map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_trivial_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_trivial_rigidDataH1Pow (solution)
