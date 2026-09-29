-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_galoisRep_isAdicContinuous_heckeRep_gl2Rep_baseChange_tateModule_jac
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/7b616fe4-3c4f-562f-963e-9d326abff34b

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_GaloisRep_Adic
import Theorems.Thm_ModularCurve_moduleFinite_and_free_padicInt_tateModule_jH
import Theorems.Thm_ModularCurve_JH_exists_finiteDimensional_smul_eq_self_of_torsion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_galoisRep_isAdicContinuous_heckeRep_gl2Rep_baseChange_tateModule_jac
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel TensorProduct

noncomputable section

namespace FLJW1

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime]

local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

abbrev T : Type := ↥(TateModule lam (Jac q M'))

abbrev Tc : Type := ↥(TateModule lam (jacComp q M'))

def toPiFun (x : T q M' lam) (ζ : Idx q) : Tc q M' lam :=
  ⟨fun n => ((x : ℕ → Jac q M') n).eval ζ, fun n =>
    ⟨by
      have h := congrArg (fun P : Jac q M' => P.eval ζ) (TateModule.torsion x n)
      simpa only [Jac.eval_zsmul, Jac.eval_zero] using h,
     by
      have h := congrArg (fun P : Jac q M' => P.eval ζ) (TateModule.compat x n)
      simpa only [Jac.eval_zsmul] using h⟩⟩

omit [Fact q.Prime] [Fact lam.Prime] in
@[scoped simp] theorem toPiFun_coe (x : T q M' lam) (ζ : Idx q) (n : ℕ) :
    ((toPiFun q M' lam x ζ : Tc q M' lam) : ℕ → jacComp q M') n = ((x : ℕ → Jac q M') n).eval ζ :=
  rfl

def toPi : T q M' lam →ₗ[ℤ_[lam]] (Idx q → Tc q M' lam) where
  toFun := toPiFun q M' lam
  map_add' _ _ := funext fun _ => Subtype.ext (funext fun _ => rfl)
  map_smul' _ _ := funext fun _ => Subtype.ext (funext fun _ => rfl)

def ofPiFun (f : Idx q → Tc q M' lam) : T q M' lam :=
  ⟨fun n => Jac.mk fun ζ => ((f ζ : Tc q M' lam) : ℕ → jacComp q M') n, fun n =>
    ⟨Jac.ext fun ζ => by
        simp only [Jac.eval_zsmul, Jac.eval_mk, Jac.eval_zero]
        exact TateModule.torsion (f ζ) n,
     Jac.ext fun ζ => by
        simp only [Jac.eval_zsmul, Jac.eval_mk]
        exact TateModule.compat (f ζ) n⟩⟩

def piEquiv : T q M' lam ≃ₗ[ℤ_[lam]] (Idx q → Tc q M' lam) :=
  { toPi q M' lam with
    invFun := ofPiFun q M' lam
    left_inv := fun _ => Subtype.ext (funext fun _ => Jac.ext fun _ => rfl)
    right_inv := fun _ => funext fun _ => Subtype.ext (funext fun _ => rfl) }

theorem finite_free [NeZero M'] :
    Module.Finite ℤ_[lam] (T q M' lam) ∧ Module.Free ℤ_[lam] (T q M' lam) := by
  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  obtain ⟨hfin, hfree⟩ := ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH (q ^ 2 * M') lam
    (levelH q M')
  haveI : Module.Finite ℤ_[lam] (Tc q M' lam) := hfin
  haveI : Module.Free ℤ_[lam] (Tc q M' lam) := hfree
  exact ⟨Module.Finite.equiv (piEquiv q M' lam).symm, Module.Free.of_equiv (piEquiv q M' lam).symm⟩

section BaseChange

variable {q M' lam}
variable (O' : Type) [CommRing O'] [Algebra ℤ_[lam] O']

omit [Fact q.Prime]

def bcMonoidHom {X : Type} [Monoid X] (φ : X →* Module.End ℤ_[lam] (T q M' lam)) :
    X →* Module.End O' (O' ⊗[ℤ_[lam]] T q M' lam) where
  toFun σ := (φ σ).baseChange O'
  map_one' := by rw [map_one, LinearMap.baseChange_one]
  map_mul' σ τ := by rw [map_mul, LinearMap.baseChange_mul]

theorem bcMonoidHom_tmul {X : Type} [Monoid X] (φ : X →* Module.End ℤ_[lam] (T q M' lam))
    (σ : X) (a : O') (x : T q M' lam) :
    bcMonoidHom O' φ σ (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] φ σ x :=
  LinearMap.baseChange_tmul _ _ _

def bcRingHom {A : Type} [Ring A] (φ : A →+* Module.End ℤ_[lam] (T q M' lam)) :
    A →+* Module.End O' (O' ⊗[ℤ_[lam]] T q M' lam) where
  toFun t := (φ t).baseChange O'
  map_one' := by rw [map_one, LinearMap.baseChange_one]
  map_mul' s t := by rw [map_mul, LinearMap.baseChange_mul]
  map_zero' := by rw [map_zero, LinearMap.baseChange_zero]
  map_add' s t := by rw [map_add, LinearMap.baseChange_add]

theorem bcRingHom_tmul {A : Type} [Ring A] (φ : A →+* Module.End ℤ_[lam] (T q M' lam))
    (t : A) (a : O') (x : T q M' lam) :
    bcRingHom O' φ t (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] φ t x :=
  LinearMap.baseChange_tmul _ _ _

theorem bcRingHom_apply_eq_zero {A : Type} [Ring A] (φ : A →+* Module.End ℤ_[lam] (T q M' lam))
    {t : A} (h : φ t = 0) : bcRingHom O' φ t = 0 := by
  show (φ t).baseChange O' = 0
  rw [h, LinearMap.baseChange_zero]

end BaseChange

def rootField : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ (Set.range (Idx.val : Idx q → AlgebraicClosure ℚ))

scoped instance finiteDimensional_rootField : FiniteDimensional ℚ (rootField q) := by
  unfold rootField
  haveI : Finite (Set.range (Idx.val : Idx q → AlgebraicClosure ℚ)) := Set.finite_range _ |>.to_subtype
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  obtain ⟨ζ, rfl⟩ := hx
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  refine ⟨Polynomial.X ^ q - Polynomial.C 1, Polynomial.monic_X_pow_sub_C (1 : ℚ) hq, ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, map_one,
    ζ.isPrimitiveRoot.pow_eq_one, sub_self]

theorem smul_idx_eq_self_of_fix {σ : Gal} (hσ : ∀ z ∈ rootField q, σ z = z) (ζ : Idx q) : σ • ζ = ζ :=
  Idx.ext (by
    rw [Idx.val_smul]
    exact hσ _ (IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self ζ)))

theorem inv_smul_idx_eq_self_of_fix {σ : Gal} (hσ : ∀ z ∈ rootField q, σ z = z) (ζ : Idx q) : σ⁻¹ • ζ = ζ := by
  conv_lhs => rw [← smul_idx_eq_self_of_fix q hσ ζ]
  rw [inv_smul_smul]

theorem exists_finiteLevel [NeZero M'] (n : ℕ) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : Gal, (∀ z ∈ L, σ z = z) →
        ∀ x : T q M' lam, galJac q M' σ ((x : ℕ → Jac q M') n) = (x : ℕ → Jac q M') n := by
  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  obtain ⟨L₁, hL₁, hfix⟩ := ModularCurve.JH.exists_finiteDimensional_smul_eq_self_of_torsion (q ^ 2 * M')
    (levelH q M') (lam ^ n) (pow_pos (Fact.out : lam.Prime).pos n)
  haveI : FiniteDimensional ℚ L₁ := hL₁
  refine ⟨L₁ ⊔ rootField q, IntermediateField.finiteDimensional_sup L₁ (rootField q), fun σ hσ x => ?_⟩
  have h₁ : ∀ z ∈ L₁, σ z = z := fun z hz => hσ z (le_sup_left (a := L₁) (b := rootField q) hz)
  have h₂ : ∀ z ∈ rootField q, σ z = z := fun z hz => hσ z (le_sup_right (a := L₁) (b := rootField q) hz)
  refine Jac.ext fun ζ => ?_
  rw [galJac_eval, inv_smul_idx_eq_self_of_fix q h₂ ζ]
  refine hfix σ h₁ _ ?_
  have ht := congrArg (fun P : Jac q M' => P.eval ζ) (TateModule.torsion x n)
  simpa only [Jac.eval_zsmul, Jac.eval_zero, Nat.cast_pow] using ht

theorem isAdicContinuous [NeZero M'] (O' : Type) [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[lam] O']
    (hlam : (lam : O') ∈ IsLocalRing.maximalIdeal O') :
    GaloisActionIsAdicContinuous O' (bcMonoidHom O' (tateGal q M' lam)) := by
  intro n
  obtain ⟨L, hL, hfix⟩ := exists_finiteLevel q M' lam n
  refine ⟨L, hL, fun σ hσ v => ?_⟩

  have key : ∀ x : T q M' lam, ∃ y : T q M' lam, ((lam : ℤ_[lam]) ^ n) • y = tateGal q M' lam σ x - x := by
    intro x
    have h0 : TateModule.proj lam (Jac q M') n (tateGal q M' lam σ x - x) = 0 := by
      rw [map_sub, sub_eq_zero, TateModule.proj_apply, TateModule.proj_apply, tateGal_apply_coe]
      exact hfix σ hσ x
    exact ⟨TateModule.shiftOfProjEqZero n _ h0, TateModule.pow_smul_shiftOfProjEqZero n _ h0⟩
  have hmem : ∀ (a : O') (x : T q M' lam),
      bcMonoidHom O' (tateGal q M' lam) σ (a ⊗ₜ[ℤ_[lam]] x) - a ⊗ₜ[ℤ_[lam]] x ∈
        (IsLocalRing.maximalIdeal O' ^ n) • (⊤ : Submodule O' (O' ⊗[ℤ_[lam]] T q M' lam)) := by
    intro a x
    obtain ⟨y, hy⟩ := key x
    have hsub : a ⊗ₜ[ℤ_[lam]] (tateGal q M' lam σ x - x) =
        a ⊗ₜ[ℤ_[lam]] tateGal q M' lam σ x - a ⊗ₜ[ℤ_[lam]] x :=
      map_sub (TensorProduct.mk ℤ_[lam] O' (T q M' lam) a) _ _
    rw [bcMonoidHom_tmul, ← hsub, ← hy, TensorProduct.tmul_smul,
      ← algebraMap_smul O' ((lam : ℤ_[lam]) ^ n) (a ⊗ₜ[ℤ_[lam]] y), map_pow, map_natCast]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hlam n) Submodule.mem_top
  induction v using TensorProduct.induction_on with
  | zero => rw [map_zero, sub_zero]; exact Submodule.zero_mem _
  | tmul a x => exact hmem a x
  | add x y hx hy =>
    rw [map_add, add_sub_add_comm]
    exact Submodule.add_mem _ hx hy

end FLJW1
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_galoisRep_isAdicContinuous_heckeRep_gl2Rep_baseChange_tateModule_jac.FLJW1"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_galoisRep_isAdicContinuous_heckeRep_gl2Rep_baseChange_tateModule_jac.FLJW1"

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (lam : ℕ) [Fact lam.Prime] :
    Module.Finite ℤ_[lam] (TateModule lam (Jac q M')) ∧
    Module.Free ℤ_[lam] (TateModule lam (Jac q M')) ∧
    ∀ (O' : Type) [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[lam] O'],
      (lam : O') ∈ IsLocalRing.maximalIdeal O' →
      ∃ (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
            Module.End O' (O' ⊗[ℤ_[lam]] TateModule lam (Jac q M')))
        (T : HeckeAlg →+* Module.End O' (O' ⊗[ℤ_[lam]] TateModule lam (Jac q M')))
        (G : CuspidalType.GL2 q →* Module.End O' (O' ⊗[ℤ_[lam]] TateModule lam (Jac q M'))),
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : O') (x : TateModule lam (Jac q M')),
            ρ σ (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] tateGal q M' lam σ x) ∧
        GaloisActionIsAdicContinuous O' ρ ∧
        (∀ (t : HeckeAlg) (a : O') (x : TateModule lam (Jac q M')),
            T t (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] tateHecke q M' lam t x) ∧
        (∀ ℓ : Nat.Primes, (ℓ : ℕ) ∣ q * M' → T (heckeGen ℓ) = 0) ∧
        (∀ (g : CuspidalType.GL2 q) (a : O') (x : TateModule lam (Jac q M')),
            G g (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] tateGL2 q M' lam g x) := by
  refine ⟨(FLJW1.finite_free q M' lam).1, (FLJW1.finite_free q M' lam).2, ?_⟩
  intro O' _ _ _ hlam
  refine ⟨FLJW1.bcMonoidHom O' (tateGal q M' lam), FLJW1.bcRingHom O' (tateHecke q M' lam),
    FLJW1.bcMonoidHom O' (tateGL2 q M' lam), FLJW1.bcMonoidHom_tmul O' _,
    FLJW1.isAdicContinuous q M' lam O' hlam, FLJW1.bcRingHom_tmul O' _, ?_, FLJW1.bcMonoidHom_tmul O' _⟩
  intro ℓ hℓ
  exact FLJW1.bcRingHom_apply_eq_zero O' _ (tateHecke_heckeGen_of_dvd q M' lam ℓ hℓ)

end S_ModularCurve_FullLevel_exists_galoisRep_isAdicContinuous_heckeRep_gl2Rep_baseChange_tateModule_jac
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_galoisRep_isAdicContinuous_heckeRep_gl2Rep_baseChange_tateModule_jac (solution)
