-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_levelModuliPackageAbs_trivial_of_isUnit_two_three_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/f1a61374-f05e-54da-a591-8cbdbb421f90

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Definitions.Def_ModularCurve_LevelNormalForm
import Theorems.Thm_WeierstrassCurve_exists_finiteType_universal_of_isUnit_discr
import Theorems.Thm_ModularCurve_LevelP_BasisRing_etale
import Theorems.Thm_ModularCurve_LevelP_BasisRing_exists_ringHom_basisData_map_eq
import Theorems.Thm_ModularCurve_LevelP_BasisRing_ringHom_ext_of_basisData_map_eq
import Theorems.Thm_ModularCurve_IsGamma0PowAt_exists_moduleFinite_represents_tuple
import Theorems.Thm_ModularCurve_IsLevelPStructure_variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_prime
import Theorems.Thm_ModularCurve_IsLevelPStructure_existsUnique_variableChange_isNormalForm
import Theorems.Thm_ModularCurve_RigidWeierstrassData_exists_levelModuliPackageAbs_surjective_of_represents_of_section
import Theorems.Thm_Algebra_IsIntegral_of_forall_valuationSubring_isDiscreteValuationRing_apply_mem
import Theorems.Thm_ModularCurve_LevelModuliPackageAbs_apply_mem_range_of_map_eq_map_univ
import Theorems.Thm_WeierstrassCurve_exists_variableChange_smul_eq_map_of_isLevelPStructure_of_jOfUnit_mem_range
import Theorems.Thm_ModularCurve_exists_map_eq_and_isGamma0PowAt_tuple_of_isGamma0PowAt_map
import Theorems.Thm_ModularCurve_exists_map_eq_and_isLevelPStructure_of_isLevelPStructure_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_levelModuliPackageAbs_trivial_of_isUnit_two_three_gamma0Pow
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Generic.isElliptic_curve"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

universe u

open ModularCurve

namespace EtPkgAsm

theorem raw_rep
    (A : Type u) [CommRing A] (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A)) (hNA : IsUnit ((N : ℕ) : A))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hN : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.FiniteType A C)
      (xᵤ : ((ModularCurve.gamma0PowComponent A N hN).prod ((ModularCurve.levelPComponent A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).toRigid.Raw C),
      ∀ (T : Type u) [CommRing T] [Algebra A T] (x : ((ModularCurve.gamma0PowComponent A N hN).prod ((ModularCurve.levelPComponent A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).toRigid.Raw T),
        ∃! ψ : C →ₐ[A] T, ((ModularCurve.gamma0PowComponent A N hN).prod ((ModularCurve.levelPComponent A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).toRigid.mapRing ψ xᵤ = x := by
  classical

  obtain ⟨S₀, _, _, _, W0, hΔ0, hunivW⟩ := WeierstrassCurve.exists_finiteType_universal_of_isUnit_discr A

  let R₁ : Type u := ModularCurve.LevelP.BasisRing W0 ℓ
  letI : Algebra A R₁ := ((algebraMap S₀ R₁).comp (algebraMap A S₀)).toAlgebra
  haveI : IsScalarTower A S₀ R₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hℓ2 : ℓ ≠ 2 := by omega
  have hℓodd : Odd ℓ := (Fact.out : ℓ.Prime).odd_of_ne_two hℓ2
  have hℓS₀ : IsUnit ((ℓ : ℕ) : S₀) := by simpa using hℓA.map (algebraMap A S₀)
  have hℓΔ : IsUnit (((ℓ : ℕ) : S₀) * W0.Δ) := hℓS₀.mul hΔ0
  haveI : Algebra.Etale S₀ R₁ := ModularCurve.LevelP.BasisRing.etale W0 hℓodd hℓΔ
  haveI : Algebra.FiniteType A R₁ := Algebra.FiniteType.trans (S := S₀) inferInstance inferInstance
  let W₁ : WeierstrassCurve R₁ := ModularCurve.LevelP.basisCurve W0 ℓ
  have hΔ₁ : IsUnit W₁.Δ := ModularCurve.LevelP.isUnit_Δ_basisCurve W0 ℓ hΔ0
  let D₁ : ModularCurve.LevelPData R₁ := ModularCurve.LevelP.basisData W0 ℓ
  have hD₁ : ModularCurve.IsLevelPStructure W₁ ℓ D₁ := ModularCurve.LevelP.isLevelPStructure_basisData W0 ℓ

  have hNR₁ : IsUnit ((N : ℕ) : R₁) := by simpa using hNA.map (algebraMap A R₁)
  have hNΔ : IsUnit (((N : ℕ) : R₁) * W₁.Δ) := hNR₁.mul hΔ₁
  obtain ⟨C₂, _, _, _, hK, hhK, hunivK⟩ :=
    ModularCurve.IsGamma0PowAt.exists_moduleFinite_represents_tuple W₁ N hNΔ
  letI : Algebra A C₂ := ((algebraMap R₁ C₂).comp (algebraMap A R₁)).toAlgebra
  haveI : IsScalarTower A R₁ C₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType A C₂ := Algebra.FiniteType.trans (S := R₁) inferInstance inferInstance
  let W₂ : WeierstrassCurve C₂ := W₁.map (algebraMap R₁ C₂)
  have hΔ₂ : IsUnit W₂.Δ := W₁.isUnit_Δ_map (algebraMap R₁ C₂) hΔ₁
  let D₂ : ModularCurve.LevelPData C₂ := D₁.map (algebraMap R₁ C₂)
  have hD₂ : ModularCurve.IsLevelPStructure W₂ ℓ D₂ := hD₁.map (algebraMap R₁ C₂)

  refine ⟨C₂, inferInstance, inferInstance, inferInstance,
    ⟨W₂, hΔ₂, ⟨hK, D₂, PUnit.unit⟩, ⟨hhK, hD₂, trivial⟩⟩, ?_⟩
  intro T _ _ x
  obtain ⟨W, hΔ, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩ := x

  have alg₀₁ : algebraMap S₀ R₁ = ModularCurve.LevelP.BasisRing.ofBase W0 ℓ := rfl
  have hW₁def : W₁ = W0.map (algebraMap S₀ R₁) := rfl

  obtain ⟨ψ₀, hψ₀W, huniq₀⟩ := hunivW T W hΔ

  have hD' : ModularCurve.IsLevelPStructure (W0.map ψ₀.toRingHom) ℓ D := by rw [hψ₀W]; exact hD
  obtain ⟨ψ₁, hψ₁c, hψ₁D⟩ :=
    ModularCurve.LevelP.BasisRing.exists_ringHom_basisData_map_eq W0 ℓ ψ₀.toRingHom D hD'
  have hW₁ : W₁.map ψ₁ = W := by
    rw [hW₁def, WeierstrassCurve.map_map, alg₀₁, hψ₁c, hψ₀W]

  have hhK' : ∀ p : ↥N.primeFactors, ModularCurve.IsGamma0PowAt (W₁.map ψ₁) (p : ℕ) (N.factorization (p : ℕ)) (h p) := by
    rw [hW₁]; exact hh
  obtain ⟨ψ₂, ⟨hψ₂c, hψ₂h⟩, huniq₂⟩ := (hunivK T ψ₁ h).mp hhK'
  have hψ₂A : ∀ a, ψ₂ (algebraMap A C₂ a) = algebraMap A T a := fun a => by
    show ψ₂ (algebraMap R₁ C₂ (algebraMap S₀ R₁ (algebraMap A S₀ a))) = algebraMap A T a
    rw [← RingHom.comp_apply ψ₂, hψ₂c, alg₀₁, ← RingHom.comp_apply ψ₁, hψ₁c]
    exact ψ₀.commutes a
  let φ₂ : C₂ →ₐ[A] T := { toRingHom := ψ₂, commutes' := hψ₂A }
  refine ⟨φ₂, ?_, ?_⟩
  ·
    refine ModularCurve.LevelComponent.Raw.ext' ?_ ?_
    · show (W₁.map (algebraMap R₁ C₂)).map ψ₂ = W
      rw [WeierstrassCurve.map_map, hψ₂c, hW₁]
    · show ((fun p : ↥N.primeFactors => (hK p).map ψ₂), (D₁.map (algebraMap R₁ C₂)).map ψ₂, PUnit.unit) = (h, D, z)
      refine Prod.ext hψ₂h (Prod.ext ?_ rfl)
      show (D₁.map (algebraMap R₁ C₂)).map ψ₂ = D
      rw [ModularCurve.LevelPData.map_map, hψ₂c, hψ₁D]
  ·
    intro ψ' hψ'
    have hc : W₂.map ψ'.toRingHom = W := congrArg ModularCurve.LevelComponent.Raw.curve hψ'
    have hl : ((fun p : ↥N.primeFactors => (hK p).map ψ'.toRingHom), D₂.map ψ'.toRingHom, PUnit.unit) = (h, D, z) :=
      congrArg ModularCurve.LevelComponent.Raw.level hψ'
    have hl₁ : (fun p : ↥N.primeFactors => (hK p).map ψ'.toRingHom) = h := congrArg Prod.fst hl
    have hl₂ : D₂.map ψ'.toRingHom = D := congrArg (fun t => t.2.1) hl
    let ψ₁' : R₁ →+* T := ψ'.toRingHom.comp (algebraMap R₁ C₂)
    let ψ₀' : S₀ →ₐ[A] T := (ψ'.comp (IsScalarTower.toAlgHom A R₁ C₂)).comp (IsScalarTower.toAlgHom A S₀ R₁)
    have hψ₀'r : ψ₀'.toRingHom = ψ₁'.comp (algebraMap S₀ R₁) := rfl

    have h0 : ψ₀' = ψ₀ := by
      apply huniq₀
      rw [hψ₀'r]
      show W0.map ((ψ'.toRingHom.comp (algebraMap R₁ C₂)).comp (algebraMap S₀ R₁)) = W
      rw [← WeierstrassCurve.map_map, ← WeierstrassCurve.map_map]
      exact hc

    have h1 : ψ₁' = ψ₁ := by
      apply ModularCurve.LevelP.BasisRing.ringHom_ext_of_basisData_map_eq W0 ℓ ψ₀.toRingHom ψ₁' ψ₁ _ hψ₁c
      · rw [hψ₁D]
        show (ModularCurve.LevelP.basisData W0 ℓ).map (ψ'.toRingHom.comp (algebraMap R₁ C₂)) = D
        rw [← ModularCurve.LevelPData.map_map]
        exact hl₂
      · rw [← alg₀₁, ← hψ₀'r, h0]

    have h2 : ψ'.toRingHom = ψ₂ := by
      apply huniq₂
      exact ⟨h1, hl₁⟩
    apply AlgHom.ext
    intro c
    exact congrArg (fun g : C₂ →+* T => g c) h2

theorem lift_dvr
    (A : Type u) [CommRing A] (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A)) (hNA : IsUnit ((N : ℕ) : A))
    (h2A : IsUnit ((2 : ℕ) : A)) (h3A : IsUnit ((3 : ℕ) : A))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hN : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (K : Type u) [Field K] [Algebra A K]
    (R₀ : Type u) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra A R₀] [Algebra R₀ K]
    [IsScalarTower A R₀ K] [IsFractionRing R₀ K]
    (x : ((ModularCurve.gamma0PowComponent A N hN).prod ((ModularCurve.levelPComponent A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).toRigid.toLevelModuliDatum.Pt K)
    (hx : ((ModularCurve.gamma0PowComponent A N hN).prod ((ModularCurve.levelPComponent A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).toRigid.toLevelModuliDatum.jOf x ∈ Set.range (algebraMap R₀ K)) :
    ∃ y : ((ModularCurve.gamma0PowComponent A N hN).prod ((ModularCurve.levelPComponent A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).toRigid.toLevelModuliDatum.Pt R₀,
      ((ModularCurve.gamma0PowComponent A N hN).prod ((ModularCurve.levelPComponent A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).toRigid.toLevelModuliDatum.map (IsScalarTower.toAlgHom A R₀ K) y = x := by
  classical
  set ι : R₀ →ₐ[A] K := IsScalarTower.toAlgHom A R₀ K with hι
  have hιK : (ι : R₀ →+* K) = algebraMap R₀ K := RingHom.ext fun r => (IsScalarTower.toAlgHom_apply A R₀ K r)
  have h2 : IsUnit ((2 : ℕ) : R₀) := by have h := h2A.map (algebraMap A R₀); rwa [map_natCast] at h
  have h3 : IsUnit ((3 : ℕ) : R₀) := by have h := h3A.map (algebraMap A R₀); rwa [map_natCast] at h
  have hℓR : IsUnit ((ℓ : ℕ) : R₀) := by simpa using hℓA.map (algebraMap A R₀)
  have hNR : IsUnit ((N : ℕ) : R₀) := by simpa using hNA.map (algebraMap A R₀)
  obtain ⟨raw, rfl⟩ := Quot.exists_rep x
  obtain ⟨W, hΔ, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩ := raw
  cases z
  have hj : W.jOfUnit hΔ ∈ Set.range (algebraMap R₀ K) := hx

  obtain ⟨C, W₀, hΔ₀, hCW⟩ := WeierstrassCurve.exists_variableChange_smul_eq_map_of_isLevelPStructure_of_jOfUnit_mem_range h2 h3 ℓ hℓ3 hℓR W hΔ hj D hD
  have hCW' : C • W = W₀.map (ι : R₀ →+* K) := by rw [hιK]; exact hCW
  have hh' : ∀ p : ↥N.primeFactors, ModularCurve.IsGamma0PowAt (W₀.map (algebraMap R₀ K)) (p : ℕ) (N.factorization (p : ℕ))
      (kernelVariableChangeDeg C (gamma0PowDeg (p : ℕ) (N.factorization (p : ℕ))) (h p)) :=
    fun p => hCW ▸ hN K W C (p : ℕ) (N.factorization (p : ℕ)) (h p) (hh p)
  have hD' : ModularCurve.IsLevelPStructure (W₀.map (algebraMap R₀ K)) ℓ (D.variableChange C) :=
    hCW ▸ hℓ K W C D hD

  obtain ⟨h₀, hh₀map, hh₀⟩ := ModularCurve.exists_map_eq_and_isGamma0PowAt_tuple_of_isGamma0PowAt_map W₀ N hNR _ hh'
  obtain ⟨D₀, hD₀map, hD₀⟩ := ModularCurve.exists_map_eq_and_isLevelPStructure_of_isLevelPStructure_map W₀ hΔ₀ ℓ hℓR _ hD'
  refine ⟨Quot.mk _ (⟨W₀, hΔ₀, ⟨h₀, D₀, PUnit.unit⟩, ⟨hh₀, hD₀, trivial⟩⟩ :
      ((gamma0PowComponent A N hN).prod ((levelPComponent A ℓ hℓ).prod (LevelComponent.trivial (A := A)))).Raw R₀), ?_⟩
  show Quot.mk _ _ = Quot.mk _ _
  have hrel : ((ModularCurve.gamma0PowComponent A N hN).prod ((ModularCurve.levelPComponent A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).toRigid.Rel
      (⟨W, hΔ, ⟨h, D, PUnit.unit⟩, ⟨hh, hD, hz⟩⟩ :
        ((gamma0PowComponent A N hN).prod ((levelPComponent A ℓ hℓ).prod (LevelComponent.trivial (A := A)))).Raw K)
      (((ModularCurve.gamma0PowComponent A N hN).prod ((ModularCurve.levelPComponent A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).toRigid.mapRing ι
        (⟨W₀, hΔ₀, ⟨h₀, D₀, PUnit.unit⟩, ⟨hh₀, hD₀, trivial⟩⟩ :
          ((gamma0PowComponent A N hN).prod ((levelPComponent A ℓ hℓ).prod (LevelComponent.trivial (A := A)))).Raw R₀)) := by
    refine ⟨C, ?_⟩
    apply LevelComponent.Raw.ext'
    · show W₀.map (ι : R₀ →+* K) = C • W
      exact hCW'.symm
    · show ((fun p : ↥N.primeFactors => (h₀ p).map (ι : R₀ →+* K)), (D₀.map (ι : R₀ →+* K), PUnit.unit)) =
        ((fun p : ↥N.primeFactors => kernelVariableChangeDeg C (gamma0PowDeg (p : ℕ) (N.factorization (p : ℕ))) (h p)),
          (D.variableChange C, PUnit.unit))
      rw [hιK, hD₀map, ← hh₀map]
  exact (Quot.sound hrel).symm

theorem val_crit
    (A : Type u) [CommRing A] (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A)) (hNA : IsUnit ((N : ℕ) : A))
    (h2A : IsUnit ((2 : ℕ) : A)) (h3A : IsUnit ((3 : ℕ) : A))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hN : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (P₀ : LevelModuliPackageAbs A ((ModularCurve.gamma0PowComponent A N hN).prod ((ModularCurve.levelPComponent A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).toRigid.toLevelModuliDatum)
    (K : Type u) [Field K] [Algebra A K] (V : ValuationSubring K) (hV : IsDiscreteValuationRing ↥V)
    (hAV : ∀ a : A, algebraMap A K a ∈ V)
    (φ : P₀.B₀ →ₐ[A] K) (hj : φ P₀.j₀ ∈ V) :
    ∀ b : P₀.B₀, φ b ∈ V := by
  classical
  intro b
  letI algAV : Algebra A ↥V := ((algebraMap A K).codRestrict V hAV).toAlgebra
  haveI : IsScalarTower A ↥V K := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI : IsDiscreteValuationRing ↥V := hV
  have hx : ((ModularCurve.gamma0PowComponent A N hN).prod ((ModularCurve.levelPComponent A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).toRigid.toLevelModuliDatum.jOf (((ModularCurve.gamma0PowComponent A N hN).prod ((ModularCurve.levelPComponent A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).toRigid.toLevelModuliDatum.map φ P₀.univ) ∈ Set.range (algebraMap ↥V K) := by
    rw [((ModularCurve.gamma0PowComponent A N hN).prod ((ModularCurve.levelPComponent A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).toRigid.toLevelModuliDatum.jOf_map]
    exact ⟨⟨φ P₀.j₀, hj⟩, rfl⟩
  obtain ⟨y, hy⟩ := lift_dvr A ℓ N hℓ3 hℓA hNA h2A h3A hℓ hN K ↥V (((ModularCurve.gamma0PowComponent A N hN).prod ((ModularCurve.levelPComponent A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).toRigid.toLevelModuliDatum.map φ P₀.univ) hx
  obtain ⟨v, hv⟩ :=
    ModularCurve.LevelModuliPackageAbs.apply_mem_range_of_map_eq_map_univ P₀ K ↥V (IsScalarTower.toAlgHom A ↥V K) φ y hy b
  rw [← hv]
  exact v.2

theorem fin_j
    (A : Type u) [CommRing A] [IsNoetherianRing A] (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A)) (hNA : IsUnit ((N : ℕ) : A))
    (h2A : IsUnit ((2 : ℕ) : A)) (h3A : IsUnit ((3 : ℕ) : A))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hN : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (P₀ : LevelModuliPackageAbs A ((ModularCurve.gamma0PowComponent A N hN).prod ((ModularCurve.levelPComponent A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).toRigid.toLevelModuliDatum)
    [Algebra.FiniteType A P₀.B₀] :
    Algebra.IsIntegral ↥(Algebra.adjoin A {P₀.j₀}) P₀.B₀ := by
  classical
  haveI : Algebra.FiniteType ↥(Algebra.adjoin A {P₀.j₀}) P₀.B₀ :=
    Algebra.FiniteType.of_restrictScalars_finiteType A ↥(Algebra.adjoin A {P₀.j₀}) P₀.B₀
  haveI : Algebra.FiniteType A ↥(Algebra.adjoin A {P₀.j₀}) :=
    ⟨(Subalgebra.fg_top _).mpr (by simpa using Subalgebra.fg_adjoin_finset (R := A) ({P₀.j₀} : Finset P₀.B₀))⟩
  haveI : IsNoetherianRing ↥(Algebra.adjoin A {P₀.j₀}) :=
    Algebra.FiniteType.isNoetherianRing A ↥(Algebra.adjoin A {P₀.j₀})
  apply Algebra.IsIntegral.of_forall_valuationSubring_isDiscreteValuationRing_apply_mem
  intro K _ V hV φ hφ b
  letI : Algebra A K := (φ.comp (algebraMap A P₀.B₀)).toAlgebra
  let φA : P₀.B₀ →ₐ[A] K := { toRingHom := φ, commutes' := fun a => rfl }
  have hAV : ∀ a : A, algebraMap A K a ∈ V := fun a =>
    hφ ⟨algebraMap A P₀.B₀ a, Subalgebra.algebraMap_mem _ a⟩
  have hj : φA P₀.j₀ ∈ V := hφ ⟨P₀.j₀, Algebra.self_mem_adjoin_singleton A P₀.j₀⟩
  exact val_crit A ℓ N hℓ3 hℓA hNA h2A h3A hℓ hN P₀ K V hV hAV φA hj b

end EtPkgAsm

open EtPkgAsm in

theorem solution
    (A : Type u) [CommRing A] [IsNoetherianRing A] (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A)) (hNA : IsUnit ((N : ℕ) : A))
    (h2A : IsUnit ((2 : ℕ) : A)) (h3A : IsUnit ((3 : ℕ) : A))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hN : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h)) :
    ∃ P : LevelModuliPackageAbs A
        ((ModularCurve.gamma0PowComponent A N hN).prod
          ((ModularCurve.levelPComponent A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).toRigid.toLevelModuliDatum,
      Algebra.FiniteType A P.B₀ ∧ Algebra.IsIntegral ↥(Algebra.adjoin A {P.j₀}) P.B₀ := by
  classical

  obtain ⟨C, instC, instAC, instFT, xᵤ, hrep⟩ := EtPkgAsm.raw_rep A ℓ N hℓ3 hℓA hNA hℓ hN

  let R : RigidWeierstrassData.{u} A := ((ModularCurve.gamma0PowComponent A N hN).prod ((ModularCurve.levelPComponent A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).toRigid

  have hrigid : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : R.Raw T) (Cv : WeierstrassCurve.VariableChange T),
      R.act Cv x = x → Cv = 1 := by
    intro T _ _ x Cv h
    have hc : Cv • x.curve = x.curve := congrArg LevelComponent.Raw.curve h
    have hl : (x.level.2.1).variableChange Cv = x.level.2.1 :=
      congrArg (fun y : R.Raw T => y.level.2.1) h
    have hℓT : IsUnit ((ℓ : ℕ) : T) := by
      simpa using hℓA.map (algebraMap A T)
    exact ModularCurve.IsLevelPStructure.variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_prime
      ℓ hℓ3 hℓT x.curve x.isUnit_Δ x.level.2.1 x.isLevel.2.1 Cv hc hl

  let NF : ∀ (T : Type u) [CommRing T] [Algebra A T], R.Raw T → Prop :=
    fun T _ _ x => ModularCurve.IsNormalForm ℓ x.curve x.level.2.1
  have hNF_map : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (x : R.Raw T), NF T x → NF T' (R.mapRing f x) := by
    intro T T' _ _ _ _ f x hx
    exact hx.map f.toRingHom
  have hNF_sec : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : R.Raw T),
      ∃! Cv : WeierstrassCurve.VariableChange T, NF T (R.act Cv x) := by
    intro T _ _ x
    have hu : IsUnit (((ℓ : ℕ) : T) * x.curve.Δ) := by
      have hℓT : IsUnit ((ℓ : ℕ) : T) := by simpa using hℓA.map (algebraMap A T)
      exact hℓT.mul x.isUnit_Δ
    exact ModularCurve.IsLevelPStructure.existsUnique_variableChange_isNormalForm
      ℓ hℓ3 x.curve hu x.level.2.1 x.isLevel.2.1

  obtain ⟨P, π, hπ⟩ :=
    ModularCurve.RigidWeierstrassData.exists_levelModuliPackageAbs_surjective_of_represents_of_section
      R C xᵤ hrep hrigid NF hNF_map hNF_sec
  refine ⟨P, ?_, ?_⟩
  · exact Algebra.FiniteType.of_surjective π hπ
  · haveI : Algebra.FiniteType A P.B₀ := Algebra.FiniteType.of_surjective π hπ
    exact EtPkgAsm.fin_j A ℓ N hℓ3 hℓA hNA h2A h3A hℓ hN P

end S_ModularCurve_FullLevel_exists_levelModuliPackageAbs_trivial_of_isUnit_two_three_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_levelModuliPackageAbs_trivial_of_isUnit_two_three_gamma0Pow (solution)
