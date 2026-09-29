-- Prove2me | solution 1 for ModularCurve.LevelModuliPackageAbs.nonempty_algEquiv_powerSeries_of_factorsThrough_trivial_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/6365738c-ec53-56ef-93df-eaca9db31013

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Theorems.Thm_ModularCurve_LevelModuliPackageAbs_existsUnique_map_comp_univ_eq_and_exists_comp_eq_of_factorsThrough
import Theorems.Thm_IsLocalRing_exists_powerSeries_algEquiv_of_forall_exists_comp_eq_of_forall_algHom_dualNumber
import Theorems.Thm_ModularCurve_FullLevel_Diamond_map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_trivial_rigidDataH1Pow
import Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_forall_eq_map_dualNumber_smul_of_trivial_rigidDataH1Pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_nonempty_algEquiv_powerSeries_of_factorsThrough_trivial_rigidDataH1Pow
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Generic.isElliptic_curve ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing ModularCurve.LevelP.instCommRingVCRing ModularCurve.LevelP.instCommRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelPRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelQRingBorelPRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingVCPolyVCRing ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatUnivBasisRingXVCRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelPRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingVCRing ModularCurve.LevelP.instAlgebraVCPolyVCRing ModularCurve.LevelP.instAlgebraBorelPRingBorelRing ModularCurve.LevelP.instAwayBorelPRingBorelDenomBorelRing"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add ModularCurve.LevelP.VCRing.lift_vcVar ModularCurve.LevelP.BorelPRing.lift_xQ ModularCurve.LevelP.twoPointLift_xQ ModularCurve.LevelP.PsiRoot.lift_ofBase ModularCurve.LevelP.univVC_u ModularCurve.LevelP.twoPointLift_yP ModularCurve.LevelP.univVC_r ModularCurve.LevelP.TorsionPointRing.lift_torsionPtX ModularCurve.LevelP.TorsionPointRing.lift_ofPsiRoot ModularCurve.LevelP.TorsionPointRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_C ModularCurve.LevelP.BorelQRing.lift_of ModularCurve.LevelP.BorelPRing.lift_yQ ModularCurve.LevelP.BorelPRing.lift_ofUniv ModularCurve.LevelP.univVC_t ModularCurve.LevelP.BorelRing.lift_ofUniv ModularCurve.LevelP.univVC_s ModularCurve.LevelP.twoPointLift_xP ModularCurve.LevelP.twoPointLift_yQ ModularCurve.LevelP.TorsionPointRing.lift_torsionPtY ModularCurve.LevelP.BorelQRing.lift_borelQY ModularCurve.LevelP.VCRing.lift_algebraMap ModularCurve.LevelP.VCRing.lift_ofUniv ModularCurve.LevelP.PsiRoot.lift_psiRootX ModularCurve.LevelP.BorelRing.lift_algebraMap"
p2m_attr_erase "simp" "ModularCurve.LevelP.BorelPRing.lift_yP ModularCurve.LevelP.BasisRing.lift_ofTwoPoint ModularCurve.LevelP.BasisRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_X ModularCurve.LevelP.genericLift_X ModularCurve.LevelP.twoPointLift_ofBase ModularCurve.LevelP.BorelPRing.lift_xP WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

open ModularCurve IsLocalRing

theorem solution
    (q : ℕ) [Fact q.Prime] (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) [NeZero M']
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
    (P : LevelModuliPackageAbs A₀
      ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum)
    (x : ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).Raw P.B₀)
    (hx : (Quot.mk _ x :
      ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).Pt P.B₀) = P.univ)

    (R₀ : Type) [CommRing R₀] [IsLocalRing R₀] [IsNoetherianRing R₀] [IsAdicComplete (maximalIdeal R₀) R₀]
    [Algebra A₀ R₀] (ι : P.B₀ →ₐ[A₀] R₀)
    (k : Type) [Field k] (hℓk : ((ℓ : ℕ) : k) ≠ 0) (hM'k : ((M' : ℕ) : k) ≠ 0)
    (resR : R₀ →+* k) (hresR : Function.Surjective resR) (hkerR : RingHom.ker resR = maximalIdeal R₀)

    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    [Algebra W₀ R₀] [Algebra A₀ W₀] [IsScalarTower A₀ W₀ R₀]
    (hresR₀ : ∀ w : W₀, resR (algebraMap W₀ R₀ w) = res₀ w)
    (hfac : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        [Algebra A₀ T] [IsScalarTower A₀ W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ φ : P.B₀ →ₐ[A₀] T, (∀ b : P.B₀, resT (φ b) = resR (ι b)) →
          ∃! Φ : R₀ →ₐ[W₀] T, (∀ r : R₀, resT (Φ r) = resR r) ∧ ∀ b : P.B₀, Φ (ι b) = φ b) :
    Nonempty (R₀ ≃ₐ[W₀] PowerSeries W₀) := by
  classical

  have hresR' : ∀ r : R₀, resR r = 0 ↔ r ∈ maximalIdeal R₀ := fun r => by rw [← RingHom.mem_ker, hkerR]
  have hres : Function.Surjective (⇑(residue R₀) ∘ ⇑(algebraMap W₀ R₀)) := by
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨w, hw⟩ := hres₀ (resR r)
    refine ⟨w, ?_⟩
    show residue R₀ (algebraMap W₀ R₀ w) = residue R₀ r
    have : algebraMap W₀ R₀ w - r ∈ maximalIdeal R₀ := by rw [← hresR', map_sub, hresR₀, hw, sub_self]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr this
  set χ : W₀ →+* ResidueField R₀ := (residue R₀).comp (algebraMap W₀ R₀) with hχdef
  have hχ : Function.Surjective χ := hres
  have hχw : ∀ w : W₀, χ w = residue R₀ (algebraMap W₀ R₀ w) := fun w => rfl

  have hnek' : ∀ n : ℕ, ((n : ℕ) : k) ≠ 0 → ((n : ℕ) : ResidueField R₀) ≠ 0 := by
    intro n hn h
    apply hn
    have h2 : residue R₀ (n : R₀) = 0 := by rw [map_natCast]; exact h
    rw [IsLocalRing.residue_eq_zero_iff] at h2
    rw [← map_natCast resR, (hresR' _).mpr h2]
  have hℓk' := hnek' ℓ hℓk
  have hM'k' := hnek' M' hM'k

  have mkRes : ∀ (T : Type) [CommRing T] [IsLocalRing T] [Algebra W₀ T],
      Function.Surjective ((residue T).comp (algebraMap W₀ T)) →
      ∃ resT : T →+* ResidueField R₀, Function.Surjective resT ∧ RingHom.ker resT = maximalIdeal T ∧
        ∀ w : W₀, resT (algebraMap W₀ T w) = χ w := by
    intro T _ _ _ hT
    have hk1 : RingHom.ker ((residue T).comp (algebraMap W₀ T)) = maximalIdeal W₀ :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hT)
    have hk2 : RingHom.ker χ = maximalIdeal W₀ :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hχ)
    let e : ResidueField T ≃+* ResidueField R₀ :=
      (RingHom.quotientKerEquivOfSurjective hT).symm.trans
        ((Ideal.quotEquivOfEq (hk1.trans hk2.symm)).trans (RingHom.quotientKerEquivOfSurjective hχ))
    refine ⟨e.toRingHom.comp (residue T), ?_, ?_, ?_⟩
    · exact e.surjective.comp Ideal.Quotient.mk_surjective
    · ext t
      rw [RingHom.mem_ker, RingHom.comp_apply]
      exact (map_eq_zero_iff e.toRingHom e.injective).trans (IsLocalRing.residue_eq_zero_iff _)
    · intro w
      show e (residue T (algebraMap W₀ T w)) = χ w
      simp only [e, RingEquiv.trans_apply]
      rw [show residue T (algebraMap W₀ T w) = ((residue T).comp (algebraMap W₀ T)) w from rfl,
        RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.quotEquivOfEq_mk,
        RingHom.quotientKerEquivOfSurjective_apply_mk]

  have hfac' : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
      [Algebra A₀ T] [IsScalarTower A₀ W₀ T]
      (resT : T →+* ResidueField R₀), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
      (∀ w : W₀, resT (algebraMap W₀ T w) = χ w) →
      ∀ φ : P.B₀ →ₐ[A₀] T, (∀ b : P.B₀, resT (φ b) = residue R₀ (ι b)) →
        ∃! Φ : R₀ →ₐ[W₀] T, (∀ r : R₀, resT (Φ r) = residue R₀ r) ∧ ∀ b : P.B₀, Φ (ι b) = φ b := by
    intro T _ _ _ _ _ _ resT hsT hkT hcT φ hφ
    let rb : ResidueField R₀ →+* k := Ideal.Quotient.lift (maximalIdeal R₀) resR (fun r hr => (hresR' r).mpr hr)
    have hrb : ∀ r : R₀, rb (residue R₀ r) = resR r := fun r => rfl
    have hrbinj : Function.Injective rb := rb.injective
    have hs' : Function.Surjective (rb.comp resT) := by
      intro z
      obtain ⟨r, rfl⟩ := hresR z
      obtain ⟨t, ht⟩ := hsT (residue R₀ r)
      exact ⟨t, by rw [RingHom.comp_apply, ht, hrb]⟩
    have hk' : RingHom.ker (rb.comp resT) = maximalIdeal T := by
      rw [← hkT]; ext t
      rw [RingHom.mem_ker, RingHom.mem_ker, RingHom.comp_apply]
      exact map_eq_zero_iff rb hrbinj
    have hc' : ∀ w : W₀, (rb.comp resT) (algebraMap W₀ T w) = res₀ w := fun w => by
      rw [RingHom.comp_apply, hcT, hχw, hrb, hresR₀]
    obtain ⟨Φ, ⟨h1, h2⟩, huniq⟩ := hfac T (rb.comp resT) hs' hk' hc' φ (fun b => by rw [RingHom.comp_apply, hφ, hrb])
    refine ⟨Φ, ⟨fun r => hrbinj (by rw [hrb]; exact h1 r), h2⟩, fun Φ' hΦ' => huniq Φ' ⟨fun r => ?_, hΦ'.2⟩⟩
    rw [RingHom.comp_apply, hΦ'.1 r, hrb]

  have PR := fun (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T] [Algebra A₀ T]
      [IsScalarTower A₀ W₀ T] (resT : T →+* ResidueField R₀) (hsT : Function.Surjective resT)
      (hkT : RingHom.ker resT = maximalIdeal T) (hcT : ∀ w : W₀, resT (algebraMap W₀ T w) = χ w) =>
    ModularCurve.LevelModuliPackageAbs.existsUnique_map_comp_univ_eq_and_exists_comp_eq_of_factorsThrough
      P R₀ ι (ResidueField R₀) (residue R₀) W₀ χ hfac' T resT hsT hkT hcT

  have hsmooth : ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
      [IsArtinianRing A] [IsArtinianRing B] [Algebra W₀ A] [Algebra W₀ B],
      Function.Surjective (⇑(residue A) ∘ ⇑(algebraMap W₀ A)) →
      Function.Surjective (⇑(residue B) ∘ ⇑(algebraMap W₀ B)) →
      ∀ π : B →ₐ[W₀] A, Function.Surjective π →
      (∀ x ∈ RingHom.ker π, ∀ y ∈ maximalIdeal B, x * y = 0) →
      ∀ g : R₀ →ₐ[W₀] A, ∃ g' : R₀ →ₐ[W₀] B, π.comp g' = g := by
    intro A B _ _ _ _ _ _ _ _ hA hB π hπ hsmall g
    letI : Algebra A₀ A := ((algebraMap W₀ A).comp (algebraMap A₀ W₀)).toAlgebra
    haveI : IsScalarTower A₀ W₀ A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI : Algebra A₀ B := ((algebraMap W₀ B).comp (algebraMap A₀ W₀)).toAlgebra
    haveI : IsScalarTower A₀ W₀ B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    obtain ⟨resA, hsA, hkA, hcA⟩ := mkRes A hA
    obtain ⟨resB, hsB, hkB, hcB⟩ := mkRes B hB

    have hπloc : ∀ m ∈ maximalIdeal B, π m ∈ maximalIdeal A := by
      have hmax : (Ideal.comap π.toRingHom (maximalIdeal A)).IsMaximal := Ideal.comap_isMaximal_of_surjective _ hπ
      have heq := IsLocalRing.eq_maximalIdeal hmax
      intro m hm
      rw [← heq] at hm
      exact hm
    have hπres : ∀ t : B, resA (π t) = resB t := by
      intro t
      obtain ⟨w, hw⟩ := hB (residue B t)
      have ht : t - algebraMap W₀ B w ∈ maximalIdeal B := by
        rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]; exact hw.symm
      have h1 : resB t = χ w := by
        have : t - algebraMap W₀ B w ∈ RingHom.ker resB := by rw [hkB]; exact ht
        rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
        rw [this, hcB]
      have h2 : resA (π t) = χ w := by
        have hm : π t - algebraMap W₀ A w ∈ maximalIdeal A := by
          have := hπloc _ ht
          rwa [map_sub, AlgHom.commutes] at this
        have : π t - algebraMap W₀ A w ∈ RingHom.ker resA := by rw [hkA]; exact hm
        rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
        rw [this, hcA]
      rw [h1, h2]

    have hgres : ∀ r : R₀, resA (g r) = residue R₀ r := by
      have hsurjg : Function.Surjective (resA.comp g.toRingHom) := by
        intro z
        obtain ⟨w, hw⟩ := hχ z
        refine ⟨algebraMap W₀ R₀ w, ?_⟩
        rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, hcA]
        exact hw
      have hkg : RingHom.ker (resA.comp g.toRingHom) = maximalIdeal R₀ :=
        IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurjg)
      intro r
      obtain ⟨w, hw⟩ := hres (residue R₀ r)
      have hr : r - algebraMap W₀ R₀ w ∈ maximalIdeal R₀ := by
        rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]; exact hw.symm
      have : r - algebraMap W₀ R₀ w ∈ RingHom.ker (resA.comp g.toRingHom) := by rw [hkg]; exact hr
      rw [RingHom.mem_ker, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, map_sub, sub_eq_zero,
        AlgHom.commutes, hcA] at this
      rw [this]
      exact hw

    have hunitA : ∀ n : ℕ, ((n : ℕ) : ResidueField R₀) ≠ 0 → IsUnit ((n : ℕ) : A) := by
      intro n hn
      by_contra hu
      have hm : ((n : ℕ) : A) ∈ maximalIdeal A := hu
      have : ((n : ℕ) : A) ∈ RingHom.ker resA := by rw [hkA]; exact hm
      rw [RingHom.mem_ker, map_natCast] at this
      exact hn this

    have hnil : ∃ n : ℕ, RingHom.ker (π.restrictScalars A₀).toRingHom ^ n = ⊥ := by
      refine ⟨2, ?_⟩
      rw [show RingHom.ker (π.restrictScalars A₀).toRingHom ^ 2 =
          RingHom.ker (π.restrictScalars A₀).toRingHom * RingHom.ker (π.restrictScalars A₀).toRingHom from pow_two _,
        eq_bot_iff, Ideal.mul_le]
      intro x hx y hy
      have hy0 : π y = 0 := hy
      have hy' : y ∈ maximalIdeal B := by
        intro hu
        have := hu.map π
        rw [hy0] at this
        exact not_isUnit_zero this
      rw [Ideal.mem_bot]
      exact hsmall x hx y hy'

    obtain ⟨y', hy'⟩ := ModularCurve.FullLevel.Diamond.map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_trivial_rigidDataH1Pow
      ℓ M' hℓ5 A₀ hℓ hM hL (π.restrictScalars A₀) hπ hnil (hunitA ℓ hℓk') (hunitA M' hM'k')
      (((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum.map ((g.restrictScalars A₀).comp ι) P.univ)
    obtain ⟨g', -, hg', -⟩ := (PR A resA hsA hkA hcA).2.2.1 B resB hsB hkB hcB π hπres g hgres y' hy'
    exact ⟨g', hg'⟩

  haveI : Module.Finite (ResidueField R₀) (DualNumber (ResidueField R₀)) := by
    change Module.Finite (ResidueField R₀) (ResidueField R₀ × ResidueField R₀); infer_instance
  haveI : IsArtinianRing (DualNumber (ResidueField R₀)) := IsArtinianRing.of_finite (ResidueField R₀) _
  set fstR : DualNumber (ResidueField R₀) →+* ResidueField R₀ :=
    (TrivSqZeroExt.fstHom (ResidueField R₀) (ResidueField R₀) (ResidueField R₀)).toRingHom with hfstR
  have hfst_s : Function.Surjective fstR := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hfst_k : RingHom.ker fstR = maximalIdeal (DualNumber (ResidueField R₀)) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective fstR hfst_s)
  have hfst_c : ∀ w : W₀, fstR (algebraMap W₀ (DualNumber (ResidueField R₀)) w) = χ w := fun w => rfl
  have PRε := PR (DualNumber (ResidueField R₀)) fstR hfst_s hfst_k hfst_c
  set fstA : DualNumber (ResidueField R₀) →ₐ[A₀] ResidueField R₀ :=
    (TrivSqZeroExt.fstHom (ResidueField R₀) (ResidueField R₀) (ResidueField R₀)).restrictScalars A₀ with hfstA
  set ρ : P.B₀ →ₐ[A₀] ResidueField R₀ := (Ideal.Quotient.mkₐ A₀ (maximalIdeal R₀)).comp ι with hρ
  have RED := PRε.2.2.2 fstA ρ (fun t => rfl) (fun b => rfl)
  set x₀ := ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum.map ρ P.univ with hx₀
  obtain ⟨y₁, hy₁, hne, huniv⟩ :=
    ModularCurve.FullLevel.Diamond.exists_forall_eq_map_dualNumber_smul_of_trivial_rigidDataH1Pow ℓ M' hℓ5 A₀ hℓ hM hL
      (ResidueField R₀) hℓk' hM'k' x₀
  obtain ⟨Φ₁, ⟨hΦ₁res, hΦ₁pt⟩, -⟩ := PRε.1 y₁ ((RED y₁).mpr hy₁)
  have hΦ₁ : ∀ r : R₀, (Φ₁ r).fst = residue R₀ r := hΦ₁res
  have hΦ₁' : ∃ r : R₀, (Φ₁ r).snd ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hne
    have hcomp : (Φ₁.restrictScalars A₀).comp ι =
        ((TrivSqZeroExt.inlAlgHom (ResidueField R₀) (ResidueField R₀) (ResidueField R₀)).restrictScalars A₀).comp ρ := by
      apply AlgHom.ext
      intro b
      show Φ₁ (ι b) = TrivSqZeroExt.inl (residue R₀ (ι b))
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [TrivSqZeroExt.fst_inl]; exact hΦ₁ (ι b)
      · rw [TrivSqZeroExt.snd_inl]; exact hall (ι b)
    rw [← hΦ₁pt, hcomp, ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum.map_comp]
  have hdim : ∀ Φ : R₀ →ₐ[W₀] DualNumber (ResidueField R₀), (∀ r : R₀, (Φ r).fst = residue R₀ r) →
      ∃ c : ResidueField R₀, ∀ r : R₀, (Φ r).snd = c * (Φ₁ r).snd := by
    intro Φ hΦ
    have hcl := PRε.2.1 Φ hΦ
    have hover : ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum.map fstA (((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum.map ((Φ.restrictScalars A₀).comp ι) P.univ) = x₀ := (RED _).mp hcl
    obtain ⟨c, hc⟩ := huniv _ hover
    let sc : DualNumber (ResidueField R₀) →ₐ[W₀] DualNumber (ResidueField R₀) :=
      (TrivSqZeroExt.map (c • (LinearMap.id : ResidueField R₀ →ₗ[ResidueField R₀] ResidueField R₀))).restrictScalars W₀
    let Ψ : R₀ →ₐ[W₀] DualNumber (ResidueField R₀) := sc.comp Φ₁
    have hΨres : ∀ r : R₀, fstR (Ψ r) = residue R₀ r := fun r => by
      show (TrivSqZeroExt.map _ (Φ₁ r)).fst = _
      rw [TrivSqZeroExt.fst_map]; exact hΦ₁ r
    have hΨpt : ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum.map ((Ψ.restrictScalars A₀).comp ι) P.univ = ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum.map ((Φ.restrictScalars A₀).comp ι) P.univ := by
      have : (Ψ.restrictScalars A₀).comp ι =
          ((TrivSqZeroExt.map (c • (LinearMap.id : ResidueField R₀ →ₗ[ResidueField R₀] ResidueField R₀))).restrictScalars A₀).comp
            ((Φ₁.restrictScalars A₀).comp ι) := AlgHom.ext fun b => rfl
      rw [this, ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum.map_comp, hΦ₁pt, ← hc]
    obtain ⟨Φ₀, -, huq⟩ := PRε.1 (((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum.map ((Φ.restrictScalars A₀).comp ι) P.univ) hcl
    have e1 : Φ = Φ₀ := huq Φ ⟨hΦ, rfl⟩
    have e2 : Ψ = Φ₀ := huq Ψ ⟨hΨres, hΨpt⟩
    refine ⟨c, fun r => ?_⟩
    have hΦΨ : Φ r = Ψ r := by rw [e1, e2]
    rw [hΦΨ]
    show (TrivSqZeroExt.map _ (Φ₁ r)).snd = c * (Φ₁ r).snd
    rw [TrivSqZeroExt.snd_map, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]

  obtain ⟨e, -⟩ := IsLocalRing.exists_powerSeries_algEquiv_of_forall_exists_comp_eq_of_forall_algHom_dualNumber
    (Λ := W₀) (R := R₀) hres hsmooth Φ₁ hΦ₁ hΦ₁' hdim
  exact ⟨e.symm⟩

end S_ModularCurve_LevelModuliPackageAbs_nonempty_algEquiv_powerSeries_of_factorsThrough_trivial_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_LevelModuliPackageAbs_nonempty_algEquiv_powerSeries_of_factorsThrough_trivial_rigidDataH1Pow (solution)
