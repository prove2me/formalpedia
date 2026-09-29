-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_pow_smul_mem_toricLattice_sup_oldLattice_of_forall_weilPairing_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/7b6fb419-df95-5df3-9f14-680906899e8e

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_CharacterLatticePairings
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jOne
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_AlgebraicCurve_Pic0_exists_weilPairing_tateModule_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_Pic0_weilPairing_tateModule_rep_semilinearAut
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Definitions.Def_ModularCurve_ShimuraKernel
import Definitions.Def_Isogeny_ConditionalCurrency
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_pair_pullbackAlong_eq_pair_pushforwardAlongHom
import Theorems.Thm_AlgebraicCurve_Pic0_weilPairing_tateModule_apply_eq_of_forall_pair_eq
import Theorems.Thm_AlgebraicCurve_Pic0_nonempty_divisorialWeilPairingData_of_isAlgClosed
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_degPts_eq_zero_of_mem_toricPts
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_AlgebraicCurve_normFormulaAlong_of_separableAlong
import Theorems.Thm_AlgebraicCurve_SemilinearAut_pullbackAlong_smul
import Theorems.Thm_PadicInt_exists_pow_smul_mem_sup_of_forall_bilinForm_apply_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_pow_smul_mem_toricLattice_sup_oldLattice_of_forall_weilPairing_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike"
p2m_attr_erase "instance" "CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap RatFunc.denom_X_pow RatFunc.powerBasisAdjoinXPow_dim RatFunc.powerBasisAdjoinXPow_gen RatFunc.intDegree_X_pow RatFunc.num_X_pow CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice"

open scoped MatrixGroups

namespace DualAssemblyH

open TateModule

variable {p : ℕ} [Fact p.Prime]
variable {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

variable (p) in

noncomputable def tmap (f : A →+ B) : TateModule p A →ₗ[ℤ_[p]] TateModule p B where
  toFun x := ⟨fun n => f ((x : ℕ → A) n), fun n =>
    ⟨by
      show ((p ^ n : ℕ) : ℤ) • f ((x : ℕ → A) n) = 0
      rw [← map_zsmul, TateModule.torsion, map_zero],
     by
      show ((p : ℕ) : ℤ) • f ((x : ℕ → A) (n + 1)) = f ((x : ℕ → A) n)
      rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => by
    show f (((x + y : TateModule p A) : ℕ → A) n) = f ((x : ℕ → A) n) + f ((y : ℕ → A) n)
    rw [TateModule.coe_add, Pi.add_apply, map_add])
  map_smul' a x := Subtype.ext (funext fun n => by
    show f (((a.appr n : ℕ) : ℤ) • (x : ℕ → A) n) = ((a.appr n : ℕ) : ℤ) • f ((x : ℕ → A) n)
    exact map_zsmul f _ _)

@[scoped simp] theorem tmap_apply (f : A →+ B) (x : TateModule p A) (n : ℕ) :
    ((tmap p f x : TateModule p B) : ℕ → B) n = f ((x : ℕ → A) n) := rfl

theorem tmap_comp (g : B →+ C) (f : A →+ B) : tmap p (g.comp f) = tmap p g ∘ₗ tmap p f :=
  LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)

theorem tmap_comp_apply (g : B →+ C) (f : A →+ B) (x : TateModule p A) :
    tmap p g (tmap p f x) = tmap p (g.comp f) x := rfl

theorem tmap_id : tmap p (AddMonoidHom.id A) = LinearMap.id :=
  LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)

theorem tmap_zero : tmap p (0 : A →+ B) = 0 :=
  LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)

theorem tmap_add (f f' : A →+ B) : tmap p (f + f') = tmap p f + tmap p f' :=
  LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)

theorem tmap_sum {ι : Type} (S : Finset ι) (D : ι → (A →+ B)) :
    tmap p (∑ i ∈ S, D i) = ∑ i ∈ S, tmap p (D i) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, tmap_zero]
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, tmap_add, ih]

theorem tmap_tmap_eq_natCast_smul_of_comp_eq_nsmul (f : A →+ B) (g : B →+ A) (c : ℕ)
    (hgf : ∀ a : A, g (f a) = c • a) (x : TateModule p A) :
    tmap p g (tmap p f x) = (c : ℤ_[p]) • x := by
  refine Subtype.ext (funext fun n => ?_)
  rw [tmap_apply, tmap_apply, hgf, TateModule.natCast_padicInt_smul_apply, natCast_zsmul]

theorem eq_tmap_of_forall_apply (f : A →+ B) (e : TateModule p A →ₗ[ℤ_[p]] TateModule p B)
    (he : ∀ (x : TateModule p A) (n : ℕ), ((e x : TateModule p B) : ℕ → B) n = f ((x : ℕ → A) n)) :
    e = tmap p f :=
  LinearMap.ext fun x => Subtype.ext (funext fun n => he x n)

theorem eq_zero_of_natCast_p_smul_eq_zero (x : TateModule p A) (h : (p : ℤ_[p]) • x = 0) : x = 0 := by
  refine Subtype.ext (funext fun n => ?_)
  have hn := congrArg (fun y : TateModule p A => (y : ℕ → A) (n + 1)) h
  beta_reduce at hn
  rw [TateModule.natCast_padicInt_smul_apply, TateModule.compat] at hn
  rw [hn]
  rfl

theorem eq_zero_of_pow_p_smul_eq_zero (e : ℕ) (x : TateModule p A) (h : ((p : ℤ_[p]) ^ e) • x = 0) :
    x = 0 := by
  induction e generalizing x with
  | zero => rwa [pow_zero, one_smul] at h
  | succ e ih =>
    rw [pow_succ, mul_smul] at h
    exact eq_zero_of_natCast_p_smul_eq_zero x (ih _ h)

theorem isUnit_natCast_padicInt_of_not_dvd {u : ℕ} (hu : ¬ p ∣ u) : IsUnit (u : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => hu ?_)
  rw [← Int.cast_natCast, PadicInt.norm_int_lt_one_iff_dvd] at hlt
  exact_mod_cast hlt

theorem eq_zero_of_natCast_smul_eq_zero {c : ℕ} (hc : c ≠ 0) (x : TateModule p A)
    (h : (c : ℤ_[p]) • x = 0) : x = 0 := by
  obtain ⟨e, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc p (Fact.out : p.Prime).ne_one
  rw [Nat.cast_mul, Nat.cast_pow, mul_comm, mul_smul] at h
  have h' : ((p : ℤ_[p]) ^ e) • x = 0 :=
    ((isUnit_natCast_padicInt_of_not_dvd hu).smul_eq_zero).mp h
  exact eq_zero_of_pow_p_smul_eq_zero e x h'

theorem tmap_injective_of_comp_eq_nsmul (f : A →+ B) (g : B →+ A) {c : ℕ} (hc : c ≠ 0)
    (hgf : ∀ a : A, g (f a) = c • a) : Function.Injective (tmap p f) := by
  intro x y hxy
  rw [← sub_eq_zero] at hxy ⊢
  rw [← map_sub] at hxy
  have h := congrArg (tmap p g) hxy
  rw [map_zero, tmap_tmap_eq_natCast_smul_of_comp_eq_nsmul f g c hgf] at h
  exact eq_zero_of_natCast_smul_eq_zero hc _ h

end DualAssemblyH
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_pow_smul_mem_toricLattice_sup_oldLattice_of_forall_weilPairing_eq_zero.DualAssemblyH"

theorem DualAssemblyH.exists_pow_eq_and_isPrimitiveRoot (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (z : AlgebraicClosure ℚ)
    (hz : IsPrimitiveRoot z (p ^ n)) : ∃ w : AlgebraicClosure ℚ, w ^ p = z ∧ IsPrimitiveRoot w (p ^ (n + 1)) := by
  rcases n with _ | n
  · have hz1 : z = 1 := by simpa using hz
    obtain ⟨w, hw⟩ := HasEnoughRootsOfUnity.prim (M := AlgebraicClosure ℚ) (n := p ^ 1)
    refine ⟨w, ?_, by simpa using hw⟩
    rw [hz1, ← pow_one p, ← hw.pow_eq_one, pow_one]
  · obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq z hp.out.pos
    refine ⟨w, hw, ?_⟩
    rw [IsPrimitiveRoot.iff_orderOf]
    refine orderOf_eq_prime_pow ?_ ?_
    · rw [pow_succ', pow_mul, hw]
      exact hz.pow_ne_one_of_pos_of_lt (pow_ne_zero _ hp.out.ne_zero) (Nat.pow_lt_pow_right hp.out.one_lt (Nat.lt_succ_self _))
    · rw [pow_succ', pow_mul, hw, hz.pow_eq_one]

theorem DualAssemblyH.exists_zeta_system (p : ℕ) [Fact p.Prime] :
    ∃ ζ : ℕ → AlgebraicClosure ℚ, (∀ n : ℕ, IsPrimitiveRoot (ζ n) (p ^ n)) ∧ ∀ n : ℕ, ζ (n + 1) ^ p = ζ n := by
  choose f hf using DualAssemblyH.exists_pow_eq_and_isPrimitiveRoot p
  let ζ : (n : ℕ) → {z : AlgebraicClosure ℚ // IsPrimitiveRoot z (p ^ n)} := fun n =>
    Nat.rec (motive := fun n => {z : AlgebraicClosure ℚ // IsPrimitiveRoot z (p ^ n)})
      ⟨1, by rw [pow_zero]; exact IsPrimitiveRoot.one⟩ (fun n zn => ⟨f n zn.1 zn.2, (hf n zn.1 zn.2).2⟩) n
  exact ⟨fun n => (ζ n).1, fun n => (ζ n).2, fun n => (hf n (ζ n).1 (ζ n).2).1⟩

noncomputable def DualAssemblyH.cycloChar (p : ℕ) [Fact p.Prime] :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* ℤ_[p]ˣ where
  toFun σ := cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv
  map_one' := by
    show cyclotomicCharacter (AlgebraicClosure ℚ) p (1 : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toRingEquiv = 1
    rw [show (1 : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toRingEquiv = 1 from rfl, map_one]
  map_mul' a b := by
    show cyclotomicCharacter (AlgebraicClosure ℚ) p (a * b).toRingEquiv = _
    rw [show (a * b).toRingEquiv = a.toRingEquiv * b.toRingEquiv from rfl, map_mul]

@[scoped simp] theorem DualAssemblyH.cycloChar_apply (p : ℕ) [Fact p.Prime] (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    DualAssemblyH.cycloChar p σ = cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv := rfl

p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_pow_smul_mem_toricLattice_sup_oldLattice_of_forall_weilPairing_eq_zero.DualAssemblyH"

theorem DualAssemblyH.hfg_xHFunctionFieldBar (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ∃ x : ↥(xHFunctionFieldBar M H), Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(xHFunctionFieldBar M H)))
        ↥(xHFunctionFieldBar M H) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ)
    (CohCarrier.GammaH M H) (translation_mem_GammaH M H)

theorem DualAssemblyH.isCurveOver_xHFunctionFieldBar (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := by
  obtain ⟨x, hx, hfin⟩ := DualAssemblyH.hfg_xHFunctionFieldBar M H
  haveI := hfin
  exact AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental x hx

namespace DualAssemblyH

theorem eq_pullbackAlongHom_of_pin {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hFI : FundamentalIdentityAlong K φ hφ)
    (g : Pic0 K F →+ Pic0 K F')
    (hpin : ∀ (Dw : Divisor.degZero (K := K) (F := F)) (Dv : Divisor.degZero (K := K) (F := F')),
      (Dv : Divisor K F') = Divisor.pullbackAlong φ hφ (Dw : Divisor K F) → g (Pic0.mk Dw) = Pic0.mk Dv) :
    ∀ x : Pic0 K F, g x = Pic0.pullbackAlongHom φ hφ hFI x := by
  intro x
  obtain ⟨Dw, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.pullbackAlongHom_mk]
  exact hpin Dw ⟨Divisor.pullbackAlong φ hφ (Dw : Divisor K F), Divisor.pullbackAlong_mem_degZero φ hφ hFI Dw.2⟩ rfl

theorem eq_pushforwardAlongHom_of_pin {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (hN : NormFormulaAlong K φ hfin)
    (g : Pic0 K F' →+ Pic0 K F)
    (hpin : ∀ (Dv : Divisor.degZero (K := K) (F := F')) (Dw : Divisor.degZero (K := K) (F := F)),
      (Dw : Divisor K F) = Divisor.pushforwardAlong φ hφ (Dv : Divisor K F') → g (Pic0.mk Dv) = Pic0.mk Dw) :
    ∀ y : Pic0 K F', g y = Pic0.pushforwardAlongHom φ hφ hfin hN y := by
  intro y
  obtain ⟨Dv, rfl⟩ := Pic0.mk_surjective y
  rw [Pic0.pushforwardAlongHom_mk]
  exact hpin Dv (Pic0.pushforwardAlongDegZero φ hφ Dv) (Pic0.coe_pushforwardAlongDegZero φ hφ Dv)

theorem pullbackAlongHom_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ) {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (hgg' : SemilinearAut.IntertwinesAlong φ.toRingHom g g') (x : Pic0 K F) :
    Pic0.pullbackAlongHom φ hφ hFI (g • x) = g' • Pic0.pullbackAlongHom φ hφ hFI x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [SemilinearAut.pic0_smul_mk, Pic0.pullbackAlongHom_mk, Pic0.pullbackAlongHom_mk, SemilinearAut.pic0_smul_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  show Divisor.pullbackAlong φ hφ (g • (D : Divisor K F)) =
    g' • Divisor.pullbackAlong φ hφ (D : Divisor K F)
  exact SemilinearAut.pullbackAlong_smul φ hφ hgg' (D : Divisor K F)

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

theorem pair_eq_pair_of_pin {K F F' : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    [IsCurveOver K F] [Field F'] [Algebra K F'] [IsCurveOver K F']
    (u : F →ₐ[K] F') (hu : u.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K u hu) (hfin : FiniteAlong K u) (hN : NormFormulaAlong K u hfin)
    (Pl : Pic0 K F →+ Pic0 K F') (Ps : Pic0 K F' →+ Pic0 K F)
    (hPl : ∀ x, Pl x = Pic0.pullbackAlongHom u hu hFI x) (hPs : ∀ y, Ps y = Pic0.pushforwardAlongHom u hu hfin hN y)
    (n : ℕ) [NeZero n] (W : DivisorialWeilPairingData K F n) (W' : DivisorialWeilPairingData K F' n)
    (x Ty : Pic0.torsion K F n) (Sx y : Pic0.torsion K F' n)
    (hSx : (Sx : Pic0 K F') = Pl x) (hTy : (Ty : Pic0 K F) = Ps y) :
    W'.pair Sx y = W.pair x Ty := by
  obtain ⟨D₀, hD₀⟩ := Pic0.mk_surjective (x : Pic0 K F)
  have hx : (n : ℤ) • (x : Pic0 K F) = 0 := Pic0.mem_torsion.mp x.2
  have hy : (n : ℤ) • (y : Pic0 K F') = 0 := Pic0.mem_torsion.mp y.2
  have hSx' : (Sx : Pic0 K F') = Pic0.mk ⟨Divisor.pullbackAlong u hu (D₀ : Divisor K F),
      Divisor.pullbackAlong_mem_degZero u hu hFI D₀.2⟩ := by
    rw [hSx, hPl, ← hD₀, Pic0.pullbackAlongHom_mk]
    rfl
  have hx' : (n : ℤ) • (Sx : Pic0 K F') = 0 := Pic0.mem_torsion.mp Sx.2
  have hy₀ : (n : ℤ) • Pic0.pushforwardAlongHom u hu hfin hN (y : Pic0 K F') = 0 := by
    rw [← hPs, ← hTy]; exact Pic0.mem_torsion.mp Ty.2
  have h := DivisorialWeilPairingData.pair_pullbackAlong_eq_pair_pushforwardAlongHom u hu hFI hfin hN W' W
    (x : Pic0 K F) hx (y : Pic0 K F') hy D₀ hD₀ (Sx : Pic0 K F') hSx' hx' hy₀
  have hTy' : Ty = ⟨Pic0.pushforwardAlongHom u hu hfin hN (y : Pic0 K F'), Pic0.mem_torsion.mpr hy₀⟩ :=
    Subtype.ext (hTy.trans (hPs _))
  rw [hTy']
  exact h

end DualAssemblyH
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_pow_smul_mem_toricLattice_sup_oldLattice_of_forall_weilPairing_eq_zero.DualAssemblyH"

set_option maxHeartbeats 3200000 in

theorem DualAssemblyH.exists_weilPairing_adjoint_degeneracy
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))]
    (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
    (hαfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) αH) (hβfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) βH)
    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (hdeg0 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
        (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
          Divisor.pushforwardAlong αH hαint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        O.degPts 0 (Pic0.mk Dv) = Pic0.mk Dw)
    (hdeg1 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
        (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
          Divisor.pushforwardAlong βH hβint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        O.degPts 1 (Pic0.mk Dv) = Pic0.mk Dw)
    (hpull0 : ∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))))
        (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Divisor.pullbackAlong αH hαint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) →
        αpull 0 (Pic0.mk Dw) = Pic0.mk Dv)
    (hpull1 : ∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))))
        (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Divisor.pullbackAlong βH hβint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) →
        αpull 1 (Pic0.mk Dw) = Pic0.mk Dv)
    (ζ : ℕ → AlgebraicClosure ℚ) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (p ^ n)) (hζp : ∀ n : ℕ, ζ (n + 1) ^ p = ζ n)
    (e : TateModule p (JH M H) →ₗ[ℤ_[p]] TateModule p (JH M H) →ₗ[ℤ_[p]] ℤ_[p])
    (hePin : ∀ (n : ℕ) (W : DivisorialWeilPairingData (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (p ^ n))
        (a b : TateModule p (JH M H)) (a' b' : Pic0.torsion (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (p ^ n)),
        (a' : JH M H) = (a : ℕ → JH M H) n → (b' : JH M H) = (b : ℕ → JH M H) n →
        W.pair a' b' = ζ n ^ ((e a b).appr n)) :
    ∃ e' : TateModule p (JH (M / p) (infSubgroup p M H hpM)) →ₗ[ℤ_[p]] TateModule p (JH (M / p) (infSubgroup p M H hpM)) →ₗ[ℤ_[p]] ℤ_[p],
      (∀ a b : TateModule p (JH (M / p) (infSubgroup p M H hpM)), e' b a = -(e' a b)) ∧
      (∀ a : TateModule p (JH (M / p) (infSubgroup p M H hpM)), (∀ b : TateModule p (JH (M / p) (infSubgroup p M H hpM)), e' a b = 0) → a = 0) ∧
      (∀ (a : TateModule p (JH (M / p) (infSubgroup p M H hpM))) (b : TateModule p (JH M H)),
        e (DualAssemblyH.tmap p (αpull 0) a) b = e' a (DualAssemblyH.tmap p (O.degPts 0) b)) ∧
      (∀ (a : TateModule p (JH (M / p) (infSubgroup p M H hpM))) (b : TateModule p (JH M H)),
        e (DualAssemblyH.tmap p (αpull 1) a) b = e' a (DualAssemblyH.tmap p (O.degPts 1) b)) := by
  classical
  have hfg := DualAssemblyH.hfg_xHFunctionFieldBar M H
  haveI hCurve : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    DualAssemblyH.isCurveOver_xHFunctionFieldBar M H

  haveI : CharZero ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective
  have hαsep := AlgebraicCurve.separableAlong_of_charZero αH hαint
  have hβsep := AlgebraicCurve.separableAlong_of_charZero βH hβint
  have hαFI : FundamentalIdentityAlong (AlgebraicClosure ℚ) αH hαint :=
    AlgebraicCurve.fundamentalIdentityAlong αH hαint hαfin hαsep
  have hβFI : FundamentalIdentityAlong (AlgebraicClosure ℚ) βH hβint :=
    AlgebraicCurve.fundamentalIdentityAlong βH hβint hβfin hβsep
  have hαN : NormFormulaAlong (AlgebraicClosure ℚ) αH hαfin := AlgebraicCurve.normFormulaAlong_of_separableAlong αH hαfin hαsep
  have hβN : NormFormulaAlong (AlgebraicClosure ℚ) βH hβfin := AlgebraicCurve.normFormulaAlong_of_separableAlong βH hβfin hβsep
  have hαpull0 : ∀ x, αpull 0 x = Pic0.pullbackAlongHom αH hαint hαFI x :=
    DualAssemblyH.eq_pullbackAlongHom_of_pin αH hαint hαFI (αpull 0) hpull0
  have hαpull1 : ∀ x, αpull 1 x = Pic0.pullbackAlongHom βH hβint hβFI x :=
    DualAssemblyH.eq_pullbackAlongHom_of_pin βH hβint hβFI (αpull 1) hpull1
  have hdegPts0 : ∀ y, O.degPts 0 y = Pic0.pushforwardAlongHom αH hαint hαfin hαN y :=
    DualAssemblyH.eq_pushforwardAlongHom_of_pin αH hαint hαfin hαN (O.degPts 0) hdeg0
  have hdegPts1 : ∀ y, O.degPts 1 y = Pic0.pushforwardAlongHom βH hβint hβfin hβN y :=
    DualAssemblyH.eq_pushforwardAlongHom_of_pin βH hβint hβfin hβN (O.degPts 1) hdeg1

  have hfg' := DualAssemblyH.hfg_xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)
  haveI hCurve' : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
    DualAssemblyH.isCurveOver_xHFunctionFieldBar _ _
  obtain ⟨e', he'Pin, he'Skew, he'Nondeg⟩ := AlgebraicCurve.Pic0.exists_weilPairing_tateModule_of_isCurveOver
    (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) hfg' p ζ hζ hζp
  have hW : ∀ n : ℕ, Nonempty (DivisorialWeilPairingData (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (p ^ n)) :=
    fun n => haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
      AlgebraicCurve.Pic0.nonempty_divisorialWeilPairingData_of_isAlgClosed (AlgebraicClosure ℚ) _ hfg (p ^ n)
  have hW' : ∀ n : ℕ, Nonempty (DivisorialWeilPairingData (AlgebraicClosure ℚ)
      ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (p ^ n)) :=
    fun n => haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
      AlgebraicCurve.Pic0.nonempty_divisorialWeilPairingData_of_isAlgClosed (AlgebraicClosure ℚ) _ hfg' (p ^ n)
  have hL0 : ∀ a b, e (DualAssemblyH.tmap p (αpull 0) a) b = e' a (DualAssemblyH.tmap p (O.degPts 0) b) :=
    fun a b => AlgebraicCurve.Pic0.weilPairing_tateModule_apply_eq_of_forall_pair_eq (AlgebraicClosure ℚ)
      ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) p ζ hζ e' he'Pin e hePin hW' hW
      (αpull 0) (O.degPts 0)
      (fun n W W' x Ty Sx y hSx hTy =>
        haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
        DualAssemblyH.pair_eq_pair_of_pin αH hαint hαFI hαfin hαN (αpull 0) (O.degPts 0) hαpull0 hdegPts0
          (p ^ n) W W' x Ty Sx y hSx hTy)
      (DualAssemblyH.tmap p (αpull 0)) (fun a n => rfl) (DualAssemblyH.tmap p (O.degPts 0)) (fun b n => rfl) a b
  have hL1 : ∀ a b, e (DualAssemblyH.tmap p (αpull 1) a) b = e' a (DualAssemblyH.tmap p (O.degPts 1) b) :=
    fun a b => AlgebraicCurve.Pic0.weilPairing_tateModule_apply_eq_of_forall_pair_eq (AlgebraicClosure ℚ)
      ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) p ζ hζ e' he'Pin e hePin hW' hW
      (αpull 1) (O.degPts 1)
      (fun n W W' x Ty Sx y hSx hTy =>
        haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
        DualAssemblyH.pair_eq_pair_of_pin βH hβint hβFI hβfin hβN (αpull 1) (O.degPts 1) hαpull1 hdegPts1
          (p ^ n) W W' x Ty Sx y hSx hTy)
      (DualAssemblyH.tmap p (αpull 1)) (fun a n => rfl) (DualAssemblyH.tmap p (O.degPts 1)) (fun b n => rfl) a b
  exact ⟨e', he'Skew, he'Nondeg, hL0, hL1⟩

set_option maxHeartbeats 3200000 in

theorem DualAssemblyH.weilPairing_eq_zero_of_mem_toricLattice_of_mem_oldLattice
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (Tt : Submodule ℤ_[p] (TateModule p (JH M H)))
    (hTt : ∀ x : TateModule p (JH M H), x ∈ Tt ↔ ∀ n : ℕ, TateModule.proj p (JH M H) n x ∈ O.toricPts (p ^ n))
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))]
    (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
    (hαfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) αH) (hβfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) βH)
    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (hdeg0 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
        (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
          Divisor.pushforwardAlong αH hαint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        O.degPts 0 (Pic0.mk Dv) = Pic0.mk Dw)
    (hdeg1 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
        (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
          Divisor.pushforwardAlong βH hβint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        O.degPts 1 (Pic0.mk Dv) = Pic0.mk Dw)
    (hpull0 : ∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))))
        (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Divisor.pullbackAlong αH hαint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) →
        αpull 0 (Pic0.mk Dw) = Pic0.mk Dv)
    (hpull1 : ∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))))
        (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Divisor.pullbackAlong βH hβint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) →
        αpull 1 (Pic0.mk Dw) = Pic0.mk Dv)
    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
    (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y))))
    (Told : Submodule ℤ_[p] (TateModule p (JH M H)))
    (hTold : ∀ x : TateModule p (JH M H), x ∈ Told ↔
      ∃ w₀ w₁ : TateModule p (JH (M / p) (infSubgroup p M H hpM)), ∀ n : ℕ,
        TateModule.proj p (JH M H) n x =
          αpull 0 (TateModule.proj p (JH (M / p) (infSubgroup p M H hpM)) n w₀) +
            αpull 1 (TateModule.proj p (JH (M / p) (infSubgroup p M H hpM)) n w₁))
    (ζ : ℕ → AlgebraicClosure ℚ) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (p ^ n)) (hζp : ∀ n : ℕ, ζ (n + 1) ^ p = ζ n)
    (e : TateModule p (JH M H) →ₗ[ℤ_[p]] TateModule p (JH M H) →ₗ[ℤ_[p]] ℤ_[p])
    (hePin : ∀ (n : ℕ) (W : DivisorialWeilPairingData (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (p ^ n))
        (a b : TateModule p (JH M H)) (a' b' : Pic0.torsion (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (p ^ n)),
        (a' : JH M H) = (a : ℕ → JH M H) n → (b' : JH M H) = (b : ℕ → JH M H) n →
        W.pair a' b' = ζ n ^ ((e a b).appr n))
    (heSkew : ∀ a b : TateModule p (JH M H), e b a = -(e a b)) :
    ∀ x ∈ Tt, ∀ y ∈ Told, e x y = 0 := by
  classical
  obtain ⟨e', -, -, hL0, hL1⟩ := DualAssemblyH.exists_weilPairing_adjoint_degeneracy p M H hpM hpM2 A hA Λ O αH βH
    hαint hβint hαfin hβfin αpull hdeg0 hdeg1 hpull0 hpull1 ζ hζ hζp e hePin

  have hTP : ∀ (j : Fin 2), ∀ x ∈ Tt, DualAssemblyH.tmap p (O.degPts j) x = 0 := fun j x hx =>
    Subtype.ext (funext fun n =>
      ModularCurve.JHNeronObjectAtP.degPts_eq_zero_of_mem_toricPts p M H hpM hpM2 A hA Λ O hΛ hΛpts_add hΛptsSp_add
        n _ ((hTt x).1 hx n) j)
  have hISO : ∀ x ∈ Tt, ∀ y ∈ Told, e x y = 0 := by
    intro x hx y hy
    obtain ⟨w₀, w₁, hw⟩ := (hTold y).1 hy
    have hy' : y = DualAssemblyH.tmap p (αpull 0) w₀ + DualAssemblyH.tmap p (αpull 1) w₁ :=
      Subtype.ext (funext fun n => hw n)
    have h0 : e (DualAssemblyH.tmap p (αpull 0) w₀) x = 0 := by rw [hL0, hTP 0 x hx, map_zero]
    have h1 : e (DualAssemblyH.tmap p (αpull 1) w₁) x = 0 := by rw [hL1, hTP 1 x hx, map_zero]
    rw [hy', map_add, heSkew (DualAssemblyH.tmap p (αpull 0) w₀) x, heSkew (DualAssemblyH.tmap p (αpull 1) w₁) x, h0, h1,
      neg_zero, add_zero]

  exact hISO

set_option maxHeartbeats 1600000 in

theorem DualAssemblyH.degeneracyPullback_galois_smul
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
    (hαfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) αH) (hβfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) βH)
    (hαq : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβq : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
        ((βH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (hpull0 : ∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))))
        (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Divisor.pullbackAlong αH hαint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) →
        αpull 0 (Pic0.mk Dw) = Pic0.mk Dv)
    (hpull1 : ∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))))
        (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Divisor.pullbackAlong βH hβint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) →
        αpull 1 (Pic0.mk Dw) = Pic0.mk Dv) :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (i : Fin 2)
      (y : JH (M / p) (infSubgroup p M H hpM)), αpull i (σ • y) = σ • αpull i y := by
  haveI : CharZero ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective
  have hαFI : FundamentalIdentityAlong (AlgebraicClosure ℚ) αH hαint :=
    AlgebraicCurve.fundamentalIdentityAlong αH hαint hαfin (AlgebraicCurve.separableAlong_of_charZero αH hαint)
  have hβFI : FundamentalIdentityAlong (AlgebraicClosure ℚ) βH hβint :=
    AlgebraicCurve.fundamentalIdentityAlong βH hβint hβfin (AlgebraicCurve.separableAlong_of_charZero βH hβint)
  have hαpull0 : ∀ x, αpull 0 x = Pic0.pullbackAlongHom αH hαint hαFI x :=
    DualAssemblyH.eq_pullbackAlongHom_of_pin αH hαint hαFI (αpull 0) hpull0
  have hαpull1 : ∀ x, αpull 1 x = Pic0.pullbackAlongHom βH hβint hβFI x :=
    DualAssemblyH.eq_pullbackAlongHom_of_pin βH hβint hβFI (αpull 1) hpull1
  intro σ i y

  have hIα : SemilinearAut.IntertwinesAlong αH.toRingHom (arithmeticGalois (xHFunctionField (M / p) (infSubgroup p M H hpM)) σ)
      (arithmeticGalois (xHFunctionField M H) σ) := by
    intro x
    apply Subtype.ext
    show coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)
        ((αH x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      ((αH (arithmeticGalois (xHFunctionField (M / p) (infSubgroup p M H hpM)) σ • x) : ↥(xHFunctionFieldBar M H)) :
        LaurentSeries (AlgebraicClosure ℚ))
    rw [hαq, hαq, coe_arithmeticGalois_smul]
  have hIβ : SemilinearAut.IntertwinesAlong βH.toRingHom (arithmeticGalois (xHFunctionField (M / p) (infSubgroup p M H hpM)) σ)
      (arithmeticGalois (xHFunctionField M H) σ) := by
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    intro x
    apply Subtype.ext
    show coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)
        ((βH x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      ((βH (arithmeticGalois (xHFunctionField (M / p) (infSubgroup p M H hpM)) σ • x) : ↥(xHFunctionFieldBar M H)) :
        LaurentSeries (AlgebraicClosure ℚ))
    rw [hβq, hβq, coe_arithmeticGalois_smul, DualAssemblyH.coeffMap_qExpand]
  fin_cases i
  · show αpull 0 (σ • y) = σ • αpull 0 y
    rw [hαpull0, hαpull0, galois_smul_pic0_def, galois_smul_pic0_def]
    exact DualAssemblyH.pullbackAlongHom_smul αH hαint hαFI hIα y
  · show αpull 1 (σ • y) = σ • αpull 1 y
    rw [hαpull1, hαpull1, galois_smul_pic0_def, galois_smul_pic0_def]
    exact DualAssemblyH.pullbackAlongHom_smul βH hβint hβFI hIβ y

set_option maxHeartbeats 1600000 in

theorem DualAssemblyH.oldLattice_sep_of_degPts
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))]
    (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
    (hαfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) αH) (hβfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) βH)
    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (hdeg0 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
        (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
          Divisor.pushforwardAlong αH hαint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        O.degPts 0 (Pic0.mk Dv) = Pic0.mk Dw)
    (hdeg1 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
        (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
          Divisor.pushforwardAlong βH hβint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        O.degPts 1 (Pic0.mk Dv) = Pic0.mk Dw)
    (hpull0 : ∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))))
        (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Divisor.pullbackAlong αH hαint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) →
        αpull 0 (Pic0.mk Dw) = Pic0.mk Dv)
    (hpull1 : ∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))))
        (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Divisor.pullbackAlong βH hβint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) →
        αpull 1 (Pic0.mk Dw) = Pic0.mk Dv)
    (ζ : ℕ → AlgebraicClosure ℚ) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (p ^ n)) (hζp : ∀ n : ℕ, ζ (n + 1) ^ p = ζ n)
    (e : TateModule p (JH M H) →ₗ[ℤ_[p]] TateModule p (JH M H) →ₗ[ℤ_[p]] ℤ_[p])
    (hePin : ∀ (n : ℕ) (W : DivisorialWeilPairingData (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (p ^ n))
        (a b : TateModule p (JH M H)) (a' b' : Pic0.torsion (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (p ^ n)),
        (a' : JH M H) = (a : ℕ → JH M H) n → (b' : JH M H) = (b : ℕ → JH M H) n →
        W.pair a' b' = ζ n ^ ((e a b).appr n))
    (heSkew : ∀ a b : TateModule p (JH M H), e b a = -(e a b))
    (Told : Submodule ℤ_[p] (TateModule p (JH M H)))
    (hTold : ∀ x : TateModule p (JH M H), x ∈ Told ↔
      ∃ w₀ w₁ : TateModule p (JH (M / p) (infSubgroup p M H hpM)), ∀ n : ℕ,
        TateModule.proj p (JH M H) n x =
          αpull 0 (TateModule.proj p (JH (M / p) (infSubgroup p M H hpM)) n w₀) +
            αpull 1 (TateModule.proj p (JH (M / p) (infSubgroup p M H hpM)) n w₁))
    (hO : ∀ o ∈ Told, (∀ (j : Fin 2) (n : ℕ), O.degPts j (TateModule.proj p (JH M H) n o) = 0) → o = 0) :
    ∀ y ∈ Told, (∀ y' ∈ Told, e y y' = 0) → y = 0 := by
  obtain ⟨e', he'Skew, he'Nondeg, hL0, hL1⟩ := DualAssemblyH.exists_weilPairing_adjoint_degeneracy p M H hpM hpM2 A hA Λ O
    αH βH hαint hβint hαfin hβfin αpull hdeg0 hdeg1 hpull0 hpull1 ζ hζ hζp e hePin

  have he'NondegR : ∀ b : TateModule p (JH (M / p) (infSubgroup p M H hpM)),
      (∀ a, e' a b = 0) → b = 0 := fun b hb =>
    he'Nondeg b fun a => by rw [he'Skew, hb a, neg_zero]

  have hpullMem : ∀ (w : TateModule p (JH (M / p) (infSubgroup p M H hpM))),
      DualAssemblyH.tmap p (αpull 0) w ∈ Told ∧ DualAssemblyH.tmap p (αpull 1) w ∈ Told := fun w =>
    ⟨(hTold _).2 ⟨w, 0, fun n => by
        show αpull 0 ((w : ℕ → JH (M / p) (infSubgroup p M H hpM)) n) =
          αpull 0 ((w : ℕ → JH (M / p) (infSubgroup p M H hpM)) n) +
            αpull 1 (((0 : TateModule p (JH (M / p) (infSubgroup p M H hpM))) : ℕ → _) n)
        rw [show (((0 : TateModule p (JH (M / p) (infSubgroup p M H hpM))) : ℕ → JH (M / p) (infSubgroup p M H hpM)) n) = 0
          from rfl, map_zero, add_zero]⟩,
     (hTold _).2 ⟨0, w, fun n => by
        show αpull 1 ((w : ℕ → JH (M / p) (infSubgroup p M H hpM)) n) =
          αpull 0 (((0 : TateModule p (JH (M / p) (infSubgroup p M H hpM))) : ℕ → _) n) +
            αpull 1 ((w : ℕ → JH (M / p) (infSubgroup p M H hpM)) n)
        rw [show (((0 : TateModule p (JH (M / p) (infSubgroup p M H hpM))) : ℕ → JH (M / p) (infSubgroup p M H hpM)) n) = 0
          from rfl, map_zero, zero_add]⟩⟩
  intro y hy hy'
  have hpush : ∀ j : Fin 2, DualAssemblyH.tmap p (O.degPts j) y = 0 := by
    intro j
    refine he'NondegR _ fun w => ?_
    fin_cases j
    · show e' w (DualAssemblyH.tmap p (O.degPts 0) y) = 0
      rw [← hL0, heSkew y, hy' _ (hpullMem w).1, neg_zero]
    · show e' w (DualAssemblyH.tmap p (O.degPts 1) y) = 0
      rw [← hL1, heSkew y, hy' _ (hpullMem w).2, neg_zero]
  refine hO y hy fun j n => ?_
  have h := congrArg (fun z : TateModule p (JH (M / p) (infSubgroup p M H hpM)) =>
    (z : ℕ → JH (M / p) (infSubgroup p M H hpM)) n) (hpush j)
  exact h

set_option maxHeartbeats 3200000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    [NeZero (M / p)]

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)

    (Tt : Submodule ℤ_[p] (TateModule p (JH M H)))
    (hTt : ∀ x : TateModule p (JH M H), x ∈ Tt ↔ ∀ n : ℕ, TateModule.proj p (JH M H) n x ∈ O.toricPts (p ^ n))
    (hDec : ∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ Tt, JH.tateGaloisRep M H p σ x ∈ Tt)

    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))]
    (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
    (hαfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) αH) (hβfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) βH)
    (hαq : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβq : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
        ((βH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (hdeg0 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
        (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
          Divisor.pushforwardAlong αH hαint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        O.degPts 0 (Pic0.mk Dv) = Pic0.mk Dw)
    (hdeg1 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
        (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
          Divisor.pushforwardAlong βH hβint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        O.degPts 1 (Pic0.mk Dv) = Pic0.mk Dw)
    (hpull0 : ∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))))
        (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Divisor.pullbackAlong αH hαint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) →
        αpull 0 (Pic0.mk Dw) = Pic0.mk Dv)
    (hpull1 : ∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))))
        (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Divisor.pullbackAlong βH hβint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) →
        αpull 1 (Pic0.mk Dw) = Pic0.mk Dv)

    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
    (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y))))

    (Told : Submodule ℤ_[p] (TateModule p (JH M H)))
    (hTold : ∀ x : TateModule p (JH M H), x ∈ Told ↔
      ∃ w₀ w₁ : TateModule p (JH (M / p) (infSubgroup p M H hpM)), ∀ n : ℕ,
        TateModule.proj p (JH M H) n x =
          αpull 0 (TateModule.proj p (JH (M / p) (infSubgroup p M H hpM)) n w₀) +
            αpull 1 (TateModule.proj p (JH (M / p) (infSubgroup p M H hpM)) n w₁))
    (hCut : ∃ k : ℕ, ∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ x : TateModule p (JH M H),
      (((p : ℕ) : ℤ_[p]) ^ k) • (JH.tateGaloisRep M H p τ x - x) ∈ Told ⊔ Tt)

    (hO : ∀ o ∈ Told, (∀ (j : Fin 2) (n : ℕ), O.degPts j (TateModule.proj p (JH M H) n o) = 0) → o = 0)

    (pull : JH M H →+ JOne M) (push : JOne M →+ JH M H) (c : ℕ) (hc : 0 < c)
    (hDEG : ∀ x : JH M H, push (pull x) = c • x)

    (ζ : ℕ → AlgebraicClosure ℚ) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (p ^ n)) (hζp : ∀ n : ℕ, ζ (n + 1) ^ p = ζ n)
    (e : TateModule p (JH M H) →ₗ[ℤ_[p]] TateModule p (JH M H) →ₗ[ℤ_[p]] ℤ_[p])
    (hePin : ∀ (n : ℕ) (W : DivisorialWeilPairingData (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (p ^ n))
        (a b : TateModule p (JH M H)) (a' b' : Pic0.torsion (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (p ^ n)),
        (a' : JH M H) = (a : ℕ → JH M H) n → (b' : JH M H) = (b : ℕ → JH M H) n →
        W.pair a' b' = ζ n ^ ((e a b).appr n))
    (heSkew : ∀ a b : TateModule p (JH M H), e b a = -(e a b))
    (heNondeg : ∀ a : TateModule p (JH M H), (∀ b : TateModule p (JH M H), e a b = 0) → a = 0) :
    ∃ k : ℕ, ∀ x : TateModule p (JH M H), (∀ y ∈ Tt, e x y = 0) → (((p : ℕ) : ℤ_[p]) ^ k) • x ∈ Tt ⊔ Told := by
  classical

  haveI hFG : Module.Finite ℤ_[p] (TateModule p (JH M H)) := by
    haveI := ModularCurve.moduleFinite_padicInt_tateModule_jOne M p
    exact Module.Finite.of_injective (DualAssemblyH.tmap p pull)
      (DualAssemblyH.tmap_injective_of_comp_eq_nsmul pull push hc.ne' hDEG)

  let Γ := ↥(A.decompositionSubgroup ℚ)
  let ρΓ : Γ →* Module.End ℤ_[p] (TateModule p (JH M H)) :=
    (JH.tateGaloisRep M H p).comp (A.decompositionSubgroup ℚ).subtype
  let χΓ : Γ →* ℤ_[p]ˣ := (DualAssemblyH.cycloChar p).comp (A.decompositionSubgroup ℚ).subtype
  let I : Subgroup Γ := A.inertiaSubgroup ℚ
  let Φ : Set Γ := {φ | A.IsFrobeniusAt (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) p}
  have hfg := DualAssemblyH.hfg_xHFunctionFieldBar M H
  haveI hCurve : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := DualAssemblyH.isCurveOver_xHFunctionFieldBar M H

  have hGAL : ∀ (γ : Γ) (a b : TateModule p (JH M H)),
      e (ρΓ γ a) (ρΓ γ b) = ((χΓ γ : ℤ_[p]ˣ) : ℤ_[p]) * e a b := by
    intro γ a b
    have h := AlgebraicCurve.Pic0.weilPairing_tateModule_rep_semilinearAut (AlgebraicClosure ℚ)
      ↥(xHFunctionFieldBar M H) hfg p ζ hζ hζp e hePin
      (ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField M H)
        ((γ : Γ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
      ((cyclotomicCharacter (AlgebraicClosure ℚ) p
        ((γ : Γ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toRingEquiv : ℤ_[p]ˣ) : ℤ_[p])
      (fun n => cyclotomicCharacter.spec p
        ((γ : Γ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toRingEquiv (ζ n) (hζ n).pow_eq_one) a b
    exact h

  have hTtΓ : ∀ (γ : Γ), ∀ x ∈ Tt, ρΓ γ x ∈ Tt := fun γ x hx => hDec γ γ.2 x hx

  have hOLDGAL := DualAssemblyH.degeneracyPullback_galois_smul p M H hpM αH βH hαint hβint hαfin hβfin hαq hβq αpull hpull0 hpull1

  have hToldI : ∀ γ ∈ I, ∀ y ∈ Told, ρΓ γ y ∈ Told := by
    intro γ _ y hy
    obtain ⟨w₀, w₁, hw⟩ := (hTold y).1 hy
    refine (hTold _).2 ⟨JH.tateGaloisRep (M / p) (infSubgroup p M H hpM) p (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) w₀,
      JH.tateGaloisRep (M / p) (infSubgroup p M H hpM) p (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) w₁, fun n => ?_⟩
    have hn : (y : ℕ → JH M H) n =
        αpull 0 ((w₀ : ℕ → JH (M / p) (infSubgroup p M H hpM)) n) +
          αpull 1 ((w₁ : ℕ → JH (M / p) (infSubgroup p M H hpM)) n) := hw n
    show (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • ((y : ℕ → JH M H) n) =
      αpull 0 ((γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • ((w₀ : ℕ → JH (M / p) (infSubgroup p M H hpM)) n)) +
        αpull 1 ((γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • ((w₁ : ℕ → JH (M / p) (infSubgroup p M H hpM)) n))
    rw [hOLDGAL, hOLDGAL, hn]
    exact smul_add _ _ _

  have hISO : ∀ x ∈ Tt, ∀ y ∈ Told, e x y = 0 :=
    DualAssemblyH.weilPairing_eq_zero_of_mem_toricLattice_of_mem_oldLattice p M H hpM hpM2 A hA Λ O hΛ Tt hTt αH βH hαint hβint
      hαfin hβfin αpull hdeg0 hdeg1 hpull0 hpull1 hΛpts_add hΛptsSp_add Told hTold ζ hζ hζp e hePin heSkew

  have hCUT : ∃ k : ℕ, ∀ τ ∈ I, ∀ v : TateModule p (JH M H), ((p : ℤ_[p]) ^ k) • (ρΓ τ v - v) ∈ Tt ⊔ Told := by
    obtain ⟨k, hk⟩ := hCut
    refine ⟨k, fun τ hτ v => ?_⟩
    have hmem : ((τ : Γ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ :=
      Subgroup.mem_map.2 ⟨τ, hτ, rfl⟩
    have h := hk _ hmem v
    rw [sup_comm] at h
    exact_mod_cast h

  have hOLD := DualAssemblyH.oldLattice_sep_of_degPts p M H hpM hpM2 A hA Λ O αH βH hαint hβint hαfin hβfin αpull hdeg0 hdeg1
    hpull0 hpull1 ζ hζ hζp e hePin heSkew Told hTold hO

  have hCYC : ∃ τ₀ ∈ I, χΓ τ₀ ≠ 1 := by
    obtain ⟨σ, hσ, hχσ⟩ := ValuationSubring.exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq A hA (-1 : ℤ_[p]ˣ)
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.1 hσ
    refine ⟨τ, hτ, fun h => ?_⟩
    have h1 : (-1 : ℤ_[p]ˣ) = 1 := hχσ.symm.trans h
    have h2 : ((-1 : ℤ_[p]ˣ) : ℤ_[p]) = ((1 : ℤ_[p]ˣ) : ℤ_[p]) := congrArg Units.val h1
    rw [Units.val_neg, Units.val_one] at h2
    norm_num at h2

  exact PadicInt.exists_pow_smul_mem_sup_of_forall_bilinForm_apply_eq_zero ρΓ χΓ I e (fun a b => by rw [heSkew]) heNondeg
    hGAL Tt Told (fun γ _ x hx => hTtΓ γ x hx) hToldI hISO hCUT hOLD hCYC

end S_ModularCurve_JHNeronObjectAtP_exists_pow_smul_mem_toricLattice_sup_oldLattice_of_forall_weilPairing_eq_zero
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_pow_smul_mem_toricLattice_sup_oldLattice_of_forall_weilPairing_eq_zero (solution)
