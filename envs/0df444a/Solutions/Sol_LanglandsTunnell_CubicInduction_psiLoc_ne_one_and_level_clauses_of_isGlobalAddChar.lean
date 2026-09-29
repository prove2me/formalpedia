-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.psiLoc_ne_one_and_level_clauses_of_isGlobalAddChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6b194bde-c7ec-56da-81da-b32622cb92aa

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Theorems.Thm_AutomorphicForm_exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_psiLoc_ne_one_and_level_clauses_of_isGlobalAddChar
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField
open LanglandsTunnell.CubicInduction NumberField.StandardAddChar

open AutomorphicForm in
theorem solution
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    psiLoc ψ v ≠ 1 ∧
    (∃ k : ℤ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp k → psiLoc ψ v x = 1) ∧
    (LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
      (∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → psiLoc ψ v x = 1) ∧
      (∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ psiLoc ψ v ((varpi v)⁻¹ * x) ≠ 1)) := by
  classical
  obtain ⟨a, ha0, ha⟩ := AutomorphicForm.exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar ℚ hψ

  obtain ⟨av, hav⟩ : ∃ av : v.adicCompletion ℚ, av = algebraMap ℚ (v.adicCompletion ℚ) a := ⟨_, rfl⟩
  have hav0 : av ≠ 0 := by rw [hav]; exact (map_ne_zero _).mpr ha0

  have hmul : ∀ x : v.adicCompletion ℚ,
      algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * adeleSingleAt ℚ v x = adeleSingleAt ℚ v (av * x) := by
    intro x
    rw [adeleSingleAt_apply, adeleSingleAt_apply]
    change ((algebraMap ℚ (InfiniteAdeleRing ℚ) a, algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) a) :
        InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) * ((0 : InfiniteAdeleRing ℚ), finAdeleSingleAt ℚ v x) =
      ((0 : InfiniteAdeleRing ℚ), finAdeleSingleAt ℚ v (av * x))
    rw [Prod.mk_mul_mk, mul_zero]
    congr 1
    apply FiniteAdeleRing.ext ℚ
    intro w
    change (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) a) w * (finAdeleSingleAt ℚ v x) w = _
    by_cases hw : w = v
    · subst hw
      rw [finAdeleSingleAt_apply_self, finAdeleSingleAt_apply_self, FiniteAdeleRing.algebraMap_apply, hav]
      rfl
    · rw [finAdeleSingleAt_apply_of_ne _ _ _ hw, finAdeleSingleAt_apply_of_ne _ _ _ hw, mul_zero]
  have key : ∀ x : v.adicCompletion ℚ, psiLoc ψ v x = psiLocal ℚ v (av * x) := by
    intro x
    show ψ (adeleSingleAt ℚ v x) = stdAddChar ℚ (adeleSingleAt ℚ v (av * x))
    rw [ha, hmul]

  have hne : psiLoc ψ v ≠ 1 := by
    intro h
    apply LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ v
    ext y
    have := congrArg (fun χ : AddChar (v.adicCompletion ℚ) ℂ => χ (av⁻¹ * y)) h
    simp only [AddChar.one_apply] at this
    rw [key, ← mul_assoc, mul_inv_cancel₀ hav0, one_mul] at this
    rw [this, AddChar.one_apply]

  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v av = WithZero.exp m := by
    have h0 : Valued.v av ≠ 0 := (Valuation.ne_zero_iff _).mpr hav0
    exact ⟨Multiplicative.toAdd (WithZero.unzero h0), (WithZero.coe_unzero h0).symm⟩
  have hk : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-m) → psiLoc ψ v x = 1 := by
    intro x hx
    rw [key]
    apply LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hm]
    calc WithZero.exp m * Valued.v x ≤ WithZero.exp m * WithZero.exp (-m) := mul_le_mul_right hx _
      _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  refine ⟨hne, ⟨-m, hk⟩, fun hlev => ?_⟩

  obtain ⟨h1, x, hx, hx1⟩ := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ v (psiLoc ψ v) ⟨-m, hk⟩ hne
  rw [hlev] at h1 hx
  refine ⟨fun y hy => h1 y (by rwa [WithZero.exp_zero]), ⟨varpi v * x, ?_, ?_⟩⟩
  · rw [map_mul]
    have hϖ : Valued.v (varpi v) = WithZero.exp (-1 : ℤ) := NumberField.AdelicLevel.valued_uniformizerUnit ℚ v
    rw [hϖ]
    calc WithZero.exp (-1 : ℤ) * Valued.v x ≤ WithZero.exp (-1 : ℤ) * WithZero.exp (0 + 1) := mul_le_mul_right hx _
      _ = 1 := by rw [← WithZero.exp_add]; norm_num
  · rwa [← mul_assoc, inv_mul_cancel₀ (varpi_ne_zero v), one_mul]

end S_LanglandsTunnell_CubicInduction_psiLoc_ne_one_and_level_clauses_of_isGlobalAddChar
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_psiLoc_ne_one_and_level_clauses_of_isGlobalAddChar (solution)
