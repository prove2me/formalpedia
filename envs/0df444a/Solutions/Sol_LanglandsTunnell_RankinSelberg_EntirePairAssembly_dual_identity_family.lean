-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.EntirePairAssembly.dual_identity_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/96572400-fe2e-5cba-aff7-c020f9bfdf6f

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift

import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_LanglandsTunnell_RankinSelberg_rsFinIntegral_eq_LFun_rsDatum_mul_rsFinIntegral_indicator
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiV
import Theorems.Thm_LanglandsTunnell_Converse_integral_unipotentQuotient_eq_rsArchIntegral_mul_rsFinIntegral_of_integrable
import Theorems.Thm_LanglandsTunnell_Converse_integrable_rsFinIntegrand_or_rsArchIntegral_eq_zero_of_integrable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_EntirePairAssembly_dual_identity_family
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instCountableOfNumberField_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"
set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_EntirePairAssembly_dual_identity_family.LanglandsTunnell LanglandsTunnell.Converse"
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
p2m_open "LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_EntirePairAssembly_dual_identity_family.LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory"
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

p2m_open "NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_EntirePairAssembly_dual_identity_family.LanglandsTunnell LanglandsTunnell.Converse"

section Ws23FactFSupply

open IsDedekindDomain NumberField Matrix AutomorphicForm
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_EntirePairAssembly_dual_identity_family.LanglandsTunnell LanglandsTunnell.CubicInduction"
open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker

noncomputable section

namespace Ws23FactF

theorem glMap_apply {A B : Type*} [CommRing A] [CommRing B] {n : Type*} [Fintype n] [DecidableEq n]
    (φ : A →+* B) (g : GL n A) (i j : n) :
    ((Matrix.GeneralLinearGroup.map φ g : GL n B) : Matrix n n B) i j = φ ((g : Matrix n n A) i j) := rfl

theorem map_iotaGL {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (g : GL (Fin 2) A) :
    Matrix.GeneralLinearGroup.map φ (iotaGL g) = iotaGL (Matrix.GeneralLinearGroup.map φ g) := by
  ext i j
  rw [glMap_apply, coe_iotaGL, coe_iotaGL]
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

abbrev G2 : Type := AdelicGL2 (𝓞 ℚ) ℚ

theorem componentAt3_iota (v : HeightOneSpectrum (𝓞 ℚ)) (g : G2) :
    componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ g) = iotaGL (finComponent (𝓞 ℚ) ℚ v (glFin (𝓞 ℚ) ℚ g)) := by
  have h : finComponent (𝓞 ℚ) ℚ v (glFin (𝓞 ℚ) ℚ g) =
      Matrix.GeneralLinearGroup.map ((finAdeleEval (𝓞 ℚ) ℚ v).comp (adeleFin (𝓞 ℚ) ℚ)) g := by
    ext i j
    rfl
  rw [h]
  exact map_iotaGL _ g

theorem archComponent3_iota (g : G2) :
    archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ g) = iotaGL (glArch (𝓞 ℚ) ℚ g) :=
  map_iotaGL _ g

theorem coe_finFactor (g : G2) :
    (RSCarrier.finFactor g : G2) =
      (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g))⁻¹ * g := rfl

theorem glArch_archRealGLAt_ratArchGL2 (g : G2) :
    glArch (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g)) =
      glArch (𝓞 ℚ) ℚ g := by
  have h := (RSCarrier.finFactor g).2
  rw [mem_finiteAdelicGL2Subgroup_iff, coe_finFactor, map_mul, map_inv, inv_mul_eq_one] at h
  exact h

theorem glFin_archRealGLAt (m : GL (Fin 2) ℝ) :
    glFin (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m) = 1 :=
  glFin_adelicArchGLIncl ℚ _

end Ws23FactF

end

end Ws23FactFSupply

section Ws23DetNormSupply

open IsDedekindDomain NumberField Matrix AutomorphicForm
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_EntirePairAssembly_dual_identity_family.LanglandsTunnell LanglandsTunnell.CubicInduction"
open NumberField.AdelicLevel NumberField.AdelicVolume

noncomputable section

namespace Ws23FactF

theorem abs_det_ratArchGL2 (g : G2) :
    |(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| = archDetNorm (default : InfinitePlace ℚ) g := by
  unfold archDetNorm LanglandsTunnell.ratArchGL2
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  have hcoe : ((Matrix.GeneralLinearGroup.map
      (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).toRingHom
        (archComponent ℚ default (glArch (𝓞 ℚ) ℚ g)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).toRingHom.mapMatrix
        ((archComponent ℚ default (glArch (𝓞 ℚ) ℚ g) : GL (Fin 2) (default : InfinitePlace ℚ).Completion) :
          Matrix (Fin 2) (Fin 2) (default : InfinitePlace ℚ).Completion) := rfl
  rw [hcoe, ← RingHom.map_det, ← Real.norm_eq_abs]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).norm_map_of_map_zero (map_zero _) _

theorem detNorm_eq_archAbs_mul_finNorm (g : G2) :
    detNorm g = |(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| *
      TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (RSCarrier.finFactor g : G2)) := by
  have hg : archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g) *
      (RSCarrier.finFactor g : G2) = g := by
    rw [coe_finFactor, mul_inv_cancel_left]
  conv_lhs => rw [← hg]
  unfold detNorm
  rw [map_mul, NumberField.TateGlobal.ideleNorm_mul]
  congr 1
  have hX : glFin (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g)) ∈
      finiteIntegralGL2 (𝓞 ℚ) ℚ := by
    rw [glFin_archRealGLAt]; exact one_mem _
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult ℚ _ hX, Fintype.prod_subsingleton _ default]
  have hmult : (default : InfinitePlace ℚ).mult = 1 := by
    simp [NumberField.InfinitePlace.mult, IsTotallyReal.isReal]
  rw [hmult, pow_one, abs_det_ratArchGL2]
  unfold archDetNorm
  rw [glArch_archRealGLAt_ratArchGL2]

theorem detNorm_cpow_eq_archAbs_cpow_mul_finNorm_cpow (g : G2) (z : ℂ) :
    ((detNorm g : ℝ) : ℂ) ^ z =
      (((|(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| : ℝ) : ℂ) ^ z) *
        ((TateGlobal.ideleNorm ℚ
          (Matrix.GeneralLinearGroup.det (RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ z) := by
  rw [detNorm_eq_archAbs_mul_finNorm, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (NumberField.TateGlobal.ideleNorm_pos _).le]

end Ws23FactF

end

end Ws23DetNormSupply

section Ws23FinInvarianceSupply

p2m_open "IsDedekindDomain NumberField Matrix AutomorphicForm LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_EntirePairAssembly_dual_identity_family.LanglandsTunnell"
open NumberField.AdelicLevel MeasureTheory

noncomputable section

namespace Ws23FI

theorem ratArchGL2_mul (g k : AdelicGL2 (𝓞 ℚ) ℚ) : ratArchGL2 (g * k) = ratArchGL2 g * ratArchGL2 k := by
  unfold LanglandsTunnell.ratArchGL2
  rw [map_mul, map_mul, map_mul]

theorem ratArchGL2_coe (k : finiteAdelicGL2Subgroup ℚ) : ratArchGL2 (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [(mem_finiteAdelicGL2Subgroup_iff ℚ _).1 k.2, map_one, map_one]

theorem ratArchGL2_eq_archRealProjAt (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ratArchGL2 g = archRealProjAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) g := by
  ext i j
  rfl

theorem ratArchGL2_archRealGLAt (m : GL (Fin 2) ℝ) :
    ratArchGL2 (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m) = m := by
  rw [ratArchGL2_eq_archRealProjAt, archRealProjAt_archRealGLAt]

theorem finFactor_archRealGLAt_mul_coe (m : GL (Fin 2) ℝ) (k : finiteAdelicGL2Subgroup ℚ) :
    RSCarrier.finFactor (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m * k) = k := by
  apply Subtype.ext
  show (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ))
      (ratArchGL2 (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m * ↑k)))⁻¹ *
        (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m * ↑k) = ↑k
  rw [ratArchGL2_mul, ratArchGL2_coe, mul_one, ratArchGL2_archRealGLAt, inv_mul_cancel_left]

theorem finInvariant_or_arch_eq_zero (A : GL (Fin 2) ℝ → ℂ) (B : finiteAdelicGL2Subgroup ℚ → ℂ)
    (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hfprod : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, f g = A (ratArchGL2 g) * B (RSCarrier.finFactor g))
    (hfN : ∀ (u : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), f ((u : AdelicGL2 (𝓞 ℚ) ℚ) * g) = f g) :
    (∀ (n : RSCarrier.finUnipotent) (k : finiteAdelicGL2Subgroup ℚ),
        B ((n : finiteAdelicGL2Subgroup ℚ) * k) = B k) ∨
      (∀ m : GL (Fin 2) ℝ, A m = 0) := by
  by_cases hA : ∀ m : GL (Fin 2) ℝ, A m = 0
  · exact Or.inr hA
  · left
    push Not at hA
    obtain ⟨m, hm⟩ := hA
    intro n k
    set a := archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m with ha
    have hn : (((n : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) ∈ adelicUnipotent ℚ :=
      Subgroup.mem_subgroupOf.1 n.2
    have hcomm : a * ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
        ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) * a :=
      archRealGLAt_mul_comm_of_glArch_eq_one _ m ((mem_finiteAdelicGL2Subgroup_iff ℚ _).1 (n : finiteAdelicGL2Subgroup ℚ).2)
    have e1 : f (a * (((n : finiteAdelicGL2Subgroup ℚ) * k : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) =
        A m * B ((n : finiteAdelicGL2Subgroup ℚ) * k) := by
      rw [hfprod, ratArchGL2_mul, ratArchGL2_coe, mul_one, ha, ratArchGL2_archRealGLAt, finFactor_archRealGLAt_mul_coe]
    have e2 : f (a * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = A m * B k := by
      rw [hfprod, ratArchGL2_mul, ratArchGL2_coe, mul_one, ha, ratArchGL2_archRealGLAt, finFactor_archRealGLAt_mul_coe]
    have e3 : f (a * (((n : finiteAdelicGL2Subgroup ℚ) * k : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) =
        f (a * (k : AdelicGL2 (𝓞 ℚ) ℚ)) := by
      have hmul : (((n : finiteAdelicGL2Subgroup ℚ) * k : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
          ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) * (k : AdelicGL2 (𝓞 ℚ) ℚ) := rfl
      rw [hmul, ← mul_assoc, hcomm, mul_assoc]
      exact hfN ⟨_, hn⟩ _
    exact mul_left_cancel₀ hm (e1.symm.trans (e3.trans e2))

theorem rsArchIntegral_eq_zero_of_forall_eq_zero [MeasurableSpace (GL (Fin 2) ℝ)] (μ : Measure (GL (Fin 2) ℝ))
    (μN : Measure RSCarrier.realUnipotent) (s : ℂ) (W F : GL (Fin 2) ℝ → ℂ)
    (h : ∀ m : GL (Fin 2) ℝ,
      (W m * F m) * (((|(Matrix.GeneralLinearGroup.det m : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)) = 0) :
    RSCarrier.rsArchIntegral μ μN s W F = 0 := by
  unfold RSCarrier.rsArchIntegral RSCarrier.rsLocalIntegral
  simp only [h, integral_zero]

theorem det_coe_finUnipotent_mul (n : RSCarrier.finUnipotent) (k : finiteAdelicGL2Subgroup ℚ) :
    Matrix.GeneralLinearGroup.det ((((n : finiteAdelicGL2Subgroup ℚ) * k : finiteAdelicGL2Subgroup ℚ)) :
        AdelicGL2 (𝓞 ℚ) ℚ) =
      Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 ℚ) ℚ) := by
  have hn : (((n : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) ∈ adelicUnipotent ℚ :=
    Subgroup.mem_subgroupOf.1 n.2
  obtain ⟨t, ht⟩ := hn
  have hdet : Matrix.GeneralLinearGroup.det (((n : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
    rw [← ht]
    refine Units.ext ?_
    change Matrix.det ((unipotentGL2 (Multiplicative.toAdd t) : AdelicGL2 (𝓞 ℚ) ℚ) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) = 1
    rw [unipotentGL2_coe, Matrix.det_fin_two_of]
    ring
  have hmul : (((n : finiteAdelicGL2Subgroup ℚ) * k : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
      ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) * (k : AdelicGL2 (𝓞 ℚ) ℚ) := rfl
  rw [hmul, map_mul, hdet, one_mul]

theorem finInvariant_or_rsArchIntegral_eq_zero [MeasurableSpace (GL (Fin 2) ℝ)] (μ : Measure (GL (Fin 2) ℝ))
    (μN : Measure RSCarrier.realUnipotent) (s : ℂ)
    (WA FA : GL (Fin 2) ℝ → ℂ) (Wf Ff : finiteAdelicGL2Subgroup ℚ → ℂ) (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hfprod : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, f g =
      ((WA (ratArchGL2 g) * FA (ratArchGL2 g)) *
          (((|(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
        ((Wf (RSCarrier.finFactor g) * Ff (RSCarrier.finFactor g)) *
          ((TateGlobal.ideleNorm ℚ
            (Matrix.GeneralLinearGroup.det (RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2))))
    (hfN : ∀ (u : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), f ((u : AdelicGL2 (𝓞 ℚ) ℚ) * g) = f g) :
    (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
        Wf ((n : finiteAdelicGL2Subgroup ℚ) * g) * Ff ((n : finiteAdelicGL2Subgroup ℚ) * g) = Wf g * Ff g) ∨
      RSCarrier.rsArchIntegral μ μN s WA FA = 0 := by
  rcases finInvariant_or_arch_eq_zero
      (fun m => (WA m * FA m) * (((|(Matrix.GeneralLinearGroup.det m : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)))
      (fun k => (Wf k * Ff k) *
        ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2)))
      f hfprod hfN with hB | hA
  · left
    intro n g
    have h := hB n g
    simp only [det_coe_finUnipotent_mul] at h
    have hne : ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2)) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      exact Or.inl (Complex.ofReal_ne_zero.2 (TateGlobal.ideleNorm_pos _).ne')
    exact mul_right_cancel₀ hne h
  · exact Or.inr (rsArchIntegral_eq_zero_of_forall_eq_zero μ μN s WA FA hA)

end Ws23FI

end

end Ws23FinInvarianceSupply

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp TateLocal.stdRootNumberAt RealArchParam LDatum CubicInduction.psiLoc ratArchGL2 TateLocal.psiLocal_ne_one RankinSelberg.rsFinIntegral_eq_LFun_rsDatum_mul_rsFinIntegral_indicator TateLocal.addCharLevel_psiLocal_rat TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel Converse.integral_unipotentQuotient_eq_rsArchIntegral_mul_rsFinIntegral_of_integrable Converse.integrable_rsFinIntegrand_or_rsArchIntegral_eq_zero_of_integrable"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "inducedE1 inducedE2 inducedE3 rsEulerPoly rsDatum rsGlobalIntegral rsGlobalIntegral_def rsFinIntegral_eq_LFun_rsDatum_mul_rsFinIntegral_indicator"
namespace EntirePairAssembly
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

open LanglandsTunnell.CubicInduction AutomorphicForm MeasureTheory

theorem finFactor_coe (g : finiteAdelicGL2Subgroup ℚ) : RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) = g := by
  apply Subtype.ext
  have h1 : ratArchGL2 (g : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
    unfold LanglandsTunnell.ratArchGL2
    rw [(mem_finiteAdelicGL2Subgroup_iff ℚ _).1 g.2, map_one, map_one]
  simp only [RSCarrier.finFactor, h1, map_one, inv_one, one_mul]

private theorem _root_.LanglandsTunnell.RankinSelberg.EntirePairAssembly.detNorm_cpow_eq_archAbs_cpow_mul_finNorm_cpow (g : AdelicGL2 (𝓞 ℚ) ℚ) (z : ℂ) :
    ((detNorm g : ℝ) : ℂ) ^ z =
      (((|(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| : ℝ) : ℂ) ^ z) *
        ((TateGlobal.ideleNorm ℚ
          (Matrix.GeneralLinearGroup.det (RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ z) :=
  Ws23FactF.detNorm_cpow_eq_archAbs_cpow_mul_finNorm_cpow g z

p2m_export "LanglandsTunnell.RankinSelberg.EntirePairAssembly" "detNorm_cpow_eq_archAbs_cpow_mul_finNorm_cpow"

theorem ratArchGL2_mul_coe (g : AdelicGL2 (𝓞 ℚ) ℚ) (k : finiteAdelicGL2Subgroup ℚ) :
    ratArchGL2 (g * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = ratArchGL2 g := by
  unfold LanglandsTunnell.ratArchGL2
  rw [map_mul, (mem_finiteAdelicGL2Subgroup_iff ℚ _).1 k.2, mul_one]

theorem finFactor_mul_coe (g : AdelicGL2 (𝓞 ℚ) ℚ) (k : finiteAdelicGL2Subgroup ℚ) :
    RSCarrier.finFactor (g * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = RSCarrier.finFactor g * k := by
  apply Subtype.ext
  show _ = ((RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)) * (k : AdelicGL2 (𝓞 ℚ) ℚ)
  simp only [RSCarrier.finFactor, ratArchGL2_mul_coe, mul_assoc]

section prover2_psi
open IsDedekindDomain NumberField

theorem psiLoc_psiQ_eq_psiV (v : HeightOneSpectrum (𝓞 ℚ)) :
    LanglandsTunnell.CubicInduction.psiLoc NumberField.StandardAddChar.psiQ v = NumberField.StandardAddChar.psiV v := by
  classical
  refine DFunLike.ext _ _ fun x => ?_
  show NumberField.StandardAddChar.psiQ (NumberField.StandardAddChar.adeleSingleAt ℚ v x) = _
  rw [show NumberField.StandardAddChar.adeleSingleAt ℚ v x =
      ((0 : InfiniteAdeleRing ℚ), NumberField.StandardAddChar.finAdeleSingleAt ℚ v x) from rfl,
    NumberField.StandardAddChar.psiQ_apply]
  simp only
  rw [AddChar.map_zero_eq_one, one_mul, NumberField.StandardAddChar.psiFin_apply]
  rw [finprod_eq_single (fun w => NumberField.StandardAddChar.psiV w (NumberField.StandardAddChar.finAdeleSingleAt ℚ v x w)) v]
  · rw [NumberField.StandardAddChar.finAdeleSingleAt_apply_self]
  · intro w hw
    rw [NumberField.StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ v x hw]
    exact AddChar.map_zero_eq_one _

theorem psiLoc_psiQ_eq_psiLocal (v : HeightOneSpectrum (𝓞 ℚ)) :
    LanglandsTunnell.CubicInduction.psiLoc NumberField.StandardAddChar.psiQ v = NumberField.StandardAddChar.psiLocal ℚ v := by
  rw [psiLoc_psiQ_eq_psiV, NumberField.StandardAddChar.psiLocal_rat_eq_psiV]

theorem supply_psi (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ)) :
    (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ∀ r : p.adicCompletionIntegers ℚ,
      LanglandsTunnell.CubicInduction.psiLoc NumberField.StandardAddChar.psiQ p
        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) r) = 1) ∧
    (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ∃ r : p.adicCompletionIntegers ℚ,
      LanglandsTunnell.CubicInduction.psiLoc NumberField.StandardAddChar.psiQ p
        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) r /
          algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) ≠ 1) := by

  have key : ∀ p : HeightOneSpectrum (𝓞 ℚ),
      (∀ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (0 : ℤ) → NumberField.StandardAddChar.psiLocal ℚ p x = 1) ∧
      ∃ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧
        NumberField.StandardAddChar.psiLocal ℚ p x ≠ 1 := by
    intro p
    have h := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ p
      (NumberField.StandardAddChar.psiLocal ℚ p)
      ⟨0, fun x hx => by
        rw [NumberField.StandardAddChar.psiLocal_rat_eq_psiV]
        exact NumberField.StandardAddChar.psiV_eq_one_of_mem_integers p
          ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by simpa using hx))⟩
      (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)
    rwa [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat] at h
  refine ⟨fun p _ r => ?_, fun p hp => ?_⟩
  · rw [psiLoc_psiQ_eq_psiLocal]
    refine (key p).1 _ ?_
    rw [WithZero.exp_zero]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 r.2
  · obtain ⟨x, hx, hne⟩ := (key p).2
    have hπ' := hπ p hp
    refine ⟨⟨x * algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p), ?_⟩, ?_⟩
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hϖ p hp]
      calc Valued.v x * WithZero.exp (-1 : ℤ) ≤ WithZero.exp ((0 : ℤ) + 1) * WithZero.exp (-1 : ℤ) :=
            mul_le_mul_left hx _
        _ = 1 := by rw [← WithZero.exp_add]; norm_num
    · rw [psiLoc_psiQ_eq_psiLocal]
      show NumberField.StandardAddChar.psiLocal ℚ p
        (x * algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) /
          algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) ≠ 1
      rwa [mul_div_cancel_right₀ _ hπ']

theorem supply_psi_of_inv_eq_psiQ (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ)) :
    (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ∀ r : p.adicCompletionIntegers ℚ,
      psiLoc ψ p (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) r) = 1) ∧
    (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ∃ r : p.adicCompletionIntegers ℚ,
      psiLoc ψ p (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) r /
        algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) ≠ 1) := by
  have hneg : ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (y : p.adicCompletion ℚ),
      psiLoc ψ p y = psiLoc NumberField.StandardAddChar.psiQ p (-y) := fun p y => by
    unfold psiLoc
    rw [AddChar.compAddMonoidHom_apply, AddChar.compAddMonoidHom_apply, ← hψQ, AddChar.inv_apply,
      ← map_neg (NumberField.StandardAddChar.adeleSingleAt ℚ p), neg_neg]
  obtain ⟨h1, h2⟩ := supply_psi SQ ϖ hπ hϖ
  refine ⟨fun p hp r => ?_, fun p hp => ?_⟩
  · rw [hneg, ← map_neg (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ))]
    exact h1 p hp (-r)
  · obtain ⟨r, hr⟩ := h2 p hp
    refine ⟨-r, ?_⟩
    rw [hneg, map_neg (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ)), neg_div, neg_neg]
    exact hr

end prover2_psi

section prover2_dual
open Complex IsDedekindDomain NumberField MeasureTheory AutomorphicForm
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_EntirePairAssembly_dual_identity_family.LanglandsTunnell.RankinSelberg"
open scoped Matrix

theorem differentiableAt_Gammaℝ_of_re_pos' {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℝ s := by
  have h : Gammaℝ = fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) := funext Gammaℝ_def
  rw [h]
  refine DifferentiableAt.mul ?_ ?_
  · refine DifferentiableAt.const_cpow (by fun_prop) (Or.inl ?_)
    exact_mod_cast Real.pi_ne_zero
  · refine (differentiableAt_Gamma _ fun m hm => ?_).comp s (by fun_prop)
    have := congrArg Complex.re hm
    simp at this
    linarith

theorem differentiableAt_Gammaℂ_of_re_pos' {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℂ s := by
  have h : Gammaℂ = fun s : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-s) * Gamma s := funext Gammaℂ_def
  rw [h]
  refine DifferentiableAt.mul (DifferentiableAt.mul (by fun_prop) ?_) ?_
  · refine DifferentiableAt.const_cpow (by fun_prop) (Or.inl ?_)
    exact mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  · refine differentiableAt_Gamma _ fun m hm => ?_
    have := congrArg Complex.re hm
    simp at this
    linarith

theorem differentiableAt_multiset_map_prod' {α : Type*} (M : Multiset α) (f : α → ℂ → ℂ) (s : ℂ)
    (h : ∀ a ∈ M, DifferentiableAt ℂ (f a) s) :
    DifferentiableAt ℂ (fun z => (M.map fun a => f a z).prod) s := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (h a (Multiset.mem_cons_self a M)).mul (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

theorem differentiableAt_archFactorDual {ι : Type*} (D : LanglandsTunnell.LDatum ι) (hwf : D.WellFormed)
    {s : ℂ} (hs : D.abscissa < s.re) : DifferentiableAt ℂ D.archFactorDual s := by
  obtain ⟨-, -, -, -, hR, hC⟩ := hwf
  have h : D.archFactorDual = fun z : ℂ =>
      (D.gammaRDual.map fun μ => Gammaℝ (z + μ)).prod * (D.gammaCDual.map fun μ => Gammaℂ (z + μ)).prod :=
    funext fun z => rfl
  rw [h]
  refine DifferentiableAt.mul ?_ ?_
  · refine differentiableAt_multiset_map_prod' D.gammaRDual (fun μ z => Gammaℝ (z + μ)) s fun μ hμ => ?_
    refine (differentiableAt_Gammaℝ_of_re_pos' ?_).comp s (by fun_prop)
    have := hR μ hμ
    simp only [add_re]
    linarith
  · refine differentiableAt_multiset_map_prod' D.gammaCDual (fun μ z => Gammaℂ (z + μ)) s fun μ hμ => ?_
    refine (differentiableAt_Gammaℂ_of_re_pos' ?_).comp s (by fun_prop)
    have := hC μ hμ
    simp only [add_re]
    linarith

theorem eq_mul_archFactorDual_mul_LFunDual_of_eventually {ι : Type*} (D : LanglandsTunnell.LDatum ι)
    (hwf : D.WellFormed) (hL : DifferentiableOn ℂ D.LFunDual {s : ℂ | D.abscissa < s.re})
    (E : ℂ → ℂ) (hE : Differentiable ℂ E)
    (Λ : ℂ → ℂ) (hΛ : Differentiable ℂ Λ)
    (h : ∃ σc : ℝ, ∀ s : ℂ, σc < s.re → Λ s = E s * D.archFactorDual s * D.LFunDual s) :
    ∀ s : ℂ, D.abscissa < s.re → Λ s = E s * D.archFactorDual s * D.LFunDual s := by
  obtain ⟨σc, hσc⟩ := h
  set U : Set ℂ := {s : ℂ | D.abscissa < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt D.abscissa).isPreconnected
  have hG : DifferentiableOn ℂ (fun s => E s * D.archFactorDual s * D.LFunDual s) U := by
    intro s hs
    exact (((hE s).mul (differentiableAt_archFactorDual D hwf hs)).differentiableWithinAt).mul (hL s hs)
  set z₀ : ℂ := ((max σc D.abscissa + 1 : ℝ) : ℂ) with hz₀
  have hz₀U : z₀ ∈ U := by
    show D.abscissa < z₀.re
    rw [hz₀, ofReal_re]
    linarith [le_max_right σc D.abscissa]
  have hev : Λ =ᶠ[nhds z₀] fun s => E s * D.archFactorDual s * D.LFunDual s := by
    have hO : IsOpen {s : ℂ | σc < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : z₀ ∈ {s : ℂ | σc < s.re} := by
      show σc < z₀.re
      rw [hz₀, ofReal_re]
      linarith [le_max_left σc D.abscissa]
    filter_upwards [hO.mem_nhds hmem] with s hs
    exact hσc s hs
  have key := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hΛ.differentiableOn.analyticOnNhd hUo)
    (hG.analyticOnNhd hUo) hUc hz₀U hev
  intro s hs
  exact key hs

theorem detNorm_pos' (g : AdelicGL2 (𝓞 ℚ) ℚ) : 0 < detNorm g := NumberField.TateGlobal.ideleNorm_pos _

theorem supply_rescale {P : Type*} (φv φd : P → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφd : ∀ par g, φd par g = φv par (transposeInvN (Fin 2) g) * ((detNorm g : ℝ) : ℂ))
    (Dm : Set (AdelicGL2 (𝓞 ℚ) ℚ)) :
    ∀ par (Θ' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (s : ℂ),
      rsGlobalIntegral Dm (s + 1 / 2) (fun g => φv par (transposeInvN (Fin 2) g)) Θ' =
        rsGlobalIntegral Dm (s - 1 / 2) (φd par) Θ' := by
  intro par Θ' s
  rw [rsGlobalIntegral_def, rsGlobalIntegral_def]
  congr 1
  funext g
  have hd0 : ((detNorm g : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (detNorm_pos' g).ne'
  have e : ((detNorm g : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2) = ((detNorm g : ℝ) : ℂ) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2 - 1 / 2) := by
    rw [show s + 1 / 2 - 1 / 2 = (s - 1 / 2 - 1 / 2) + 1 by ring, Complex.cpow_add _ _ hd0, Complex.cpow_one, mul_comm]
  rw [hφd, e]
  ring

end prover2_dual

end LanglandsTunnell.RankinSelberg.EntirePairAssembly

open LanglandsTunnell.RankinSelberg.EntirePairAssembly in
open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ) (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (P : RealArchParam)
    (ω μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (_hunr : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ¬ IsRamifiedIn K p)
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)] [hIfin : ∀ p : HeightOneSpectrum (𝓞 ℚ), Fintype (𝓞 ℚ ⧸ p.asIdeal)]
    (Dm : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (c : ℂ) (hc0 : c ≠ 0)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (μf : MeasureTheory.Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
    (μNFin : MeasureTheory.Measure RSCarrier.finUnipotent) [μNFin.IsHaarMeasure]
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ))
    {n : ℕ} (φ : Fin n → AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (coef : Fin n → ℂ) (σb : ℝ)

    (Θ Wd : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (μNArch : MeasureTheory.Measure RSCarrier.realUnipotent) [μNArch.IsHaarMeasure]
      (_hsplit : MeasureTheory.Measure.map (fun g : AdelicGL2 (𝓞 ℚ) ℚ => (ratArchGL2 g, RSCarrier.finFactor g))
        (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) = RSCarrier.archMeasure.prod μf)
      (_hNsplit : MeasureTheory.Measure.map
        (fun n : adelicUnipotent ℚ => (ratArchGL2 (n : AdelicGL2 (𝓞 ℚ) ℚ), RSCarrier.finFactor n))
        (unipotentHaar ℚ) =
        (MeasureTheory.Measure.map Subtype.val μNArch).prod (MeasureTheory.Measure.map Subtype.val μNFin))
      (_hwf : (rsDatum ℚ SQ Φ.a Φ.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          (twistedGammaR K (archOfParamR K P) uR aR)
          (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
          (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
          (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
          (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).WellFormed)
      (_hLhold : DifferentiableOn ℂ (rsDatum ℚ SQ Φ.a Φ.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          (twistedGammaR K (archOfParamR K P) uR aR)
          (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
          (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
          (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
          (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).LFunDual
        {s : ℂ | (rsDatum ℚ SQ Φ.a Φ.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          (twistedGammaR K (archOfParamR K P) uR aR)
          (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
          (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
          (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
          (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).abscissa < s.re})
      (_hEd : Differentiable ℂ (fun s : ℂ => (pinnedRootNumber K (formalBaseChange ℚ K Φ) μ SK (archOfParamR K P) (archOfParamC K P)
        uR aR uC kC) *
        (((finiteConductor K μ SK) : ℝ) : ℂ) ^ (s - 1 / 2) *
        (fun t : ℂ => ∏ w : ↥SK,
        LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar (ω * μ) w.1) *
        LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar μ w.1) *
        (((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - t)) ^
        (-(LanglandsTunnell.Converse.pinnedExp K (ω * μ) w.1 + LanglandsTunnell.Converse.pinnedExp K μ w.1))) s))
      (_hconvd : (rsDatum ℚ SQ (fun p => Φ.a p / Φ.b p) (fun p => (Φ.b p)⁻¹)
        (fun 𝔓 => ((fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) 𝔓)⁻¹)
        (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
        (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
        (fun w hw => (archOfParamC K P w hw).dual)
        (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))
        (twistedGammaR K (archOfParamR K P) uR aR)
        (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)).Converges)

      (φd : Fin n → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
      (_hφd : ∀ i g, φd i g = φ i (transposeInvN (Fin 2) g) * ((detNorm g : ℝ) : ℂ))

      (hμf : finiteAdelicGL2Subgroup ℚ)
      (_hQT : ∀ f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
        (∀ (u : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), f ((u : AdelicGL2 (𝓞 ℚ) ℚ) * g) = f g) →
        (∫ q, f (Quotient.out q * (hμf : AdelicGL2 (𝓞 ℚ) ℚ)) ∂(unipotentQuotientMeasure ℚ) =
            ∫ q, f (Quotient.out q) ∂(unipotentQuotientMeasure ℚ)) ∧
          (MeasureTheory.Integrable (fun q : UnipotentQuotient ℚ => f (Quotient.out q * (hμf : AdelicGL2 (𝓞 ℚ) ℚ)))
              (unipotentQuotientMeasure ℚ) ↔
            MeasureTheory.Integrable (fun q : UnipotentQuotient ℚ => f (Quotient.out q)) (unipotentQuotientMeasure ℚ)))
      (_hPF : TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (hμf : AdelicGL2 (𝓞 ℚ) ℚ)) = finiteConductor K μ SK)
      (_hNpos : 0 < finiteConductor K μ SK)

      (WAd : Fin n → GL (Fin 2) ℝ → ℂ) (Wfd : Fin n → finiteAdelicGL2Subgroup ℚ → ℂ)
      (_hWAdf : ∀ (i : Fin n) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ (φd i) 1 g = WAd i (ratArchGL2 g) * Wfd i (RSCarrier.finFactor g))

      (_hHLd : ∀ i : Fin n,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ∀ (x : p.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor (UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.unipotent x) * g)) =
            psiLoc ψ p x * (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor g)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
          ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
            x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
              (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p x)) =
                (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor g)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ hp : p ∉ SQ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          (∑ r, (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.repSome
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp)
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ)
                (algebraMap (𝓞 ℚ) (p.adicCompletionIntegers ℚ) (Quotient.out (r : 𝓞 ℚ ⧸ p.asIdeal)))))))) +
            (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.repInf
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp)))) =
            (Φ.a p / Φ.b p) * (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor g)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ hp : p ∉ SQ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.scalarPi
            (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp)))) =
            ((Φ.b p)⁻¹ / (Ideal.absNorm p.asIdeal : ℂ)) * (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor g)))
      (FAd : Fin n → GL (Fin 2) ℝ → ℂ) (Ffd : Fin n → finiteAdelicGL2Subgroup ℚ → ℂ)
      (_hFAdf : ∀ (i : Fin n) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        Wd i (iota (𝓞 ℚ) ℚ g) = FAd i (ratArchGL2 g) * Ffd i (RSCarrier.finFactor g))

      (hHd : HeightOneSpectrum (𝓞 ℚ) → ℕ → ℂ)
      (_hHdrec : (∀ p, hHd p 0 = 1) ∧ (∀ p, hHd p 1 = inducedE1 ℚ (fun 𝔓 => ((fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) 𝔓)⁻¹) p) ∧
        (∀ p, hHd p 2 = inducedE1 ℚ (fun 𝔓 => ((fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) 𝔓)⁻¹) p ^ 2 - inducedE2 ℚ (fun 𝔓 => ((fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) 𝔓)⁻¹) p) ∧
        (∀ p (n : ℕ), hHd p (n + 3) = inducedE1 ℚ (fun 𝔓 => ((fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) 𝔓)⁻¹) p * hHd p (n + 2) - inducedE2 ℚ (fun 𝔓 => ((fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) 𝔓)⁻¹) p * hHd p (n + 1) +
          inducedE3 ℚ (fun 𝔓 => ((fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) 𝔓)⁻¹) p * hHd p n))
      (uHd : HeightOneSpectrum (𝓞 ℚ) → ℕ → ℕ → ℂ)
      (_uHdrec : (∀ p k, uHd p k 0 = hHd p k) ∧
        (∀ p k₁ k₂, uHd p k₁ (k₂ + 1) = hHd p k₁ * hHd p (k₂ + 1) - hHd p (k₁ + 1) * hHd p k₂))
      (uZd : HeightOneSpectrum (𝓞 ℚ) → ℤ → ℤ → ℂ)
      (_uZdrec : (∀ p (m₁ m₂ : ℤ), (m₂ < 0 ∨ m₁ < m₂) → uZd p m₁ m₂ = 0) ∧
        (∀ p (k₁ k₂ : ℕ), k₂ ≤ k₁ → uZd p k₁ k₂ = uHd p k₁ k₂))
      (_hTTd : ∀ i : Fin n,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
          ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
            x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
              (fun g => Ffd i (g * hμf)) (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p x)) =
                (fun g => Ffd i (g * hμf)) (RSCarrier.finFactor g)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ hp : p ∉ SQ, ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (m₁ m₂ : ℤ),
          localAt ℚ p g = 1 →
            (fun g => Ffd i (g * hμf)) (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p
                (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p))
                    (hπ p hp) (m₁ - m₂) *
                  UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p))
                    (hπ p hp) ^ m₂))) =
              (fun g => Ffd i (g * hμf)) (RSCarrier.finFactor g) * ((Ideal.absNorm p.asIdeal : ℂ)⁻¹ ^ m₁ * uZd p m₁ m₂)))

      (fd : Fin n → ℂ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
      (_hfd : ∀ i s' g, fd i s' g =
        whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ (φd i) 1 g * Wd i (iota (𝓞 ℚ) ℚ g) *
          ((detNorm g : ℝ) : ℂ) ^ (s' - 1 / 2))
      (_hJ3df : ∀ i, ∃ σ0 : ℝ, ∀ s' : ℂ, σ0 < s'.re →
        rsGlobalIntegral Dm s' (φd i) (dualForm (Θ i)) = c * ∫ q, fd i s' (Quotient.out q) ∂(unipotentQuotientMeasure ℚ))

      (_hfdm : ∀ (i : Fin n) (s' : ℂ), Measurable (fd i s'))
      (_hfdN : ∀ (i : Fin n) (s' : ℂ) (u : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        fd i s' ((u : AdelicGL2 (𝓞 ℚ) ℚ) * g) = fd i s' g)
      (_hintd7 : ∀ i : Fin n, ∃ σ7 : ℝ, ∀ s' : ℂ, σ7 < s'.re →
        MeasureTheory.Integrable (fun q : UnipotentQuotient ℚ => fd i s' (Quotient.out q)) (unipotentQuotientMeasure ℚ))

      (κd : Fin n → ℂ → ℂ)
      (_hJ5ad : ∀ i (s' : ℂ), σb < s'.re →
        RSCarrier.rsFinIntegral μf μNFin s'
          ({g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => Wfd i (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf)))
          ({g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => Ffd i (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf))) = κd i s')
      (_hJ5bd : ∀ s : ℂ, σb < s.re →
        ∑ i, coef i *
          (RSCarrier.rsArchIntegral RSCarrier.archMeasure μNArch (s - 1 / 2) (WAd i) (FAd i) * κd i (s - 1 / 2)) =
        (pinnedRootNumber K (formalBaseChange ℚ K Φ) μ SK (archOfParamR K P) (archOfParamC K P)
          uR aR uC kC) * (((finiteConductor K μ SK) : ℝ) : ℂ) ^ ((1 : ℂ) / 2) * (fun t : ℂ => ∏ w : ↥SK,
          LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar (ω * μ) w.1) *
          LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar μ w.1) *
          (((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - t)) ^
          (-(LanglandsTunnell.Converse.pinnedExp K (ω * μ) w.1 + LanglandsTunnell.Converse.pinnedExp K μ w.1))) s * (rsDatum ℚ SQ Φ.a Φ.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          (twistedGammaR K (archOfParamR K P) uR aR)
          (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
          (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
          (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
          (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).archFactorDual s)
      (_hdiff : Differentiable ℂ
        (fun s : ℂ => c⁻¹ * ∑ i, coef i * rsGlobalIntegral Dm (s - 1 / 2) (φ i) (Θ i)))
      (_hfe : ∀ s : ℂ, (c⁻¹ * ∑ i, coef i * rsGlobalIntegral Dm (s - 1 / 2) (φ i) (Θ i)) =
        c⁻¹ * ∑ i, coef i * rsGlobalIntegral Dm ((1 - s) + 1 / 2) (fun g => φ i (transposeInvN (Fin 2) g))
          (dualForm (Θ i))),
    ∀ s : ℂ, 1 < s.re →
      c⁻¹ * ∑ i, coef i *
          rsGlobalIntegral Dm (s + 1 / 2) (fun g => φ i (transposeInvN (Fin 2) g)) (dualForm (Θ i)) =
        (pinnedRootNumber K (formalBaseChange ℚ K Φ) μ SK (archOfParamR K P) (archOfParamC K P)
          uR aR uC kC) *
          (((finiteConductor K μ SK) : ℝ) : ℂ) ^ (s - 1 / 2) *
          (fun t : ℂ => ∏ w : ↥SK,
          LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar (ω * μ) w.1) *
          LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar μ w.1) *
          (((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - t)) ^
          (-(LanglandsTunnell.Converse.pinnedExp K (ω * μ) w.1 + LanglandsTunnell.Converse.pinnedExp K μ w.1))) s *
          (rsDatum ℚ SQ Φ.a Φ.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          (twistedGammaR K (archOfParamR K P) uR aR)
          (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
          (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
          (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
          (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).archFactorDual s *
          (rsDatum ℚ SQ Φ.a Φ.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          (twistedGammaR K (archOfParamR K P) uR aR)
          (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
          (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
          (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
          (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).LFunDual s := by
  intro μNArch _ hsplit hNsplit hwf hLhold hEd hconvd φd hφd hμf hQT hPF hNpos WAd Wfd hWAdf hHLd FAd Ffd hFAdf hHd hHdrec uHd uHdrec uZd uZdrec hTTd fd hfd hJ3df hfdm hfdN hintd7 κd hJ5ad hJ5bd hdiff hfe
  obtain ⟨hhd0, hhd1, hhd2, hhd3⟩ := hHdrec
  obtain ⟨hud0, hud1⟩ := uHdrec
  obtain ⟨huZdoff, huZdcone⟩ := uZdrec
  letI mR : MeasurableSpace (GL (Fin 2) ℝ) := borel _
  haveI : SecondCountableTopology (finiteAdelicGL2Subgroup ℚ) :=
    TopologicalSpace.Subtype.secondCountableTopology (finiteAdelicGL2Subgroup ℚ : Set (AdelicGL2 (𝓞 ℚ) ℚ))
  have hdetC := detNorm_cpow_eq_archAbs_cpow_mul_finNorm_cpow
  have hcoe := finFactor_coe
  haveI hIne : ∀ p : HeightOneSpectrum (𝓞 ℚ), Nonempty (𝓞 ℚ ⧸ p.asIdeal) := fun p => ⟨0⟩
  have hIcard : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Fintype.card (𝓞 ℚ ⧸ p.asIdeal) = Ideal.absNorm p.asIdeal := by
    intro p _
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

  have hRS : ∀ (i : Fin n) (Θ' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (s : ℂ),
      rsGlobalIntegral Dm (s + 1 / 2) (fun g => φ i (transposeInvN (Fin 2) g)) Θ' =
        rsGlobalIntegral Dm (s - 1 / 2) (φd i) Θ' :=
    supply_rescale φ φd hφd Dm
  have hfdprod : ∀ (i : Fin n) (s' : ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ), fd i s' g =
      ((WAd i (ratArchGL2 g) * FAd i (ratArchGL2 g)) *
          (((|(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| : ℝ) : ℂ) ^ (s' - 1 / 2))) *
        ((Wfd i (RSCarrier.finFactor g) * Ffd i (RSCarrier.finFactor g)) *
          ((TateGlobal.ideleNorm ℚ
            (Matrix.GeneralLinearGroup.det (RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s' - 1 / 2))) := by
    intro i s' g
    simp only [hfd, hWAdf, hFAdf, hdetC]
    ring

  have hN0 : (((finiteConductor K μ SK) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hNpos.ne'
  have hNe : ∀ s' : ℂ, (((finiteConductor K μ SK) : ℝ) : ℂ) ^ (s' - 1 / 2) ≠ 0 := fun s' h0 => hN0 ((Complex.cpow_eq_zero_iff _ _).1 h0).1
  obtain ⟨fd', hfdprod'⟩ : ∃ fd' : Fin n → ℂ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ, ∀ (i : Fin n) (s' : ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      fd' i s' g =
        ((WAd i (ratArchGL2 g) * FAd i (ratArchGL2 g)) *
            (((|(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| : ℝ) : ℂ) ^ (s' - 1 / 2))) *
          (((fun g => Wfd i (g * hμf)) (RSCarrier.finFactor g) * (fun g => Ffd i (g * hμf)) (RSCarrier.finFactor g)) *
            ((TateGlobal.ideleNorm ℚ
              (Matrix.GeneralLinearGroup.det (RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s' - 1 / 2))) :=
    ⟨_, fun _ _ _ => rfl⟩
  have htr : ∀ (i : Fin n) (s' : ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      fd i s' (g * (hμf : AdelicGL2 (𝓞 ℚ) ℚ)) = (((finiteConductor K μ SK) : ℝ) : ℂ) ^ (s' - 1 / 2) * fd' i s' g := by
    intro i s' g
    have hn1 : (0 : ℝ) ≤ TateGlobal.ideleNorm ℚ
        (Matrix.GeneralLinearGroup.det (RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)) := (TateGlobal.ideleNorm_pos _).le
    rw [hfdprod, hfdprod', ratArchGL2_mul_coe, finFactor_mul_coe, Subgroup.coe_mul, map_mul,
      NumberField.TateGlobal.ideleNorm_mul, hPF, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hn1 hNpos.le]
    beta_reduce
    ring
  have hfdm' : ∀ (i : Fin n) (s' : ℂ), Measurable (fd' i s') := fun i s' => by
    have heq : fd' i s' = fun g => ((((finiteConductor K μ SK) : ℝ) : ℂ) ^ (s' - 1 / 2))⁻¹ * fd i s' (g * (hμf : AdelicGL2 (𝓞 ℚ) ℚ)) := by
      funext g
      rw [htr, ← mul_assoc, inv_mul_cancel₀ (hNe s'), one_mul]
    rw [heq]
    exact ((hfdm i s').comp (measurable_mul_const _)).const_mul _
  have hfdN' : ∀ (i : Fin n) (s' : ℂ) (u : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      fd' i s' ((u : AdelicGL2 (𝓞 ℚ) ℚ) * g) = fd' i s' g := fun i s' u g => by
    have h1 := hfdN i s' u (g * (hμf : AdelicGL2 (𝓞 ℚ) ℚ))
    rw [← mul_assoc] at h1
    rw [htr, htr] at h1
    exact mul_left_cancel₀ (hNe s') h1
  choose σd7 hintd7 using hintd7
  have hintd7' : ∀ (i : Fin n) (s' : ℂ), σd7 i < s'.re →
      MeasureTheory.Integrable (fun q : UnipotentQuotient ℚ => fd' i s' (Quotient.out q)) (unipotentQuotientMeasure ℚ) :=
    fun i s' hs' => by
    have h1 := ((hQT (fd i s') (hfdN i s')).2).2 (hintd7 i s' hs')
    have heq : (fun q : UnipotentQuotient ℚ => fd i s' (Quotient.out q * (hμf : AdelicGL2 (𝓞 ℚ) ℚ))) =
        fun q => (((finiteConductor K μ SK) : ℝ) : ℂ) ^ (s' - 1 / 2) * fd' i s' (Quotient.out q) := funext fun q => htr i s' _
    rw [heq] at h1
    have h2 := h1.const_mul (((((finiteConductor K μ SK) : ℝ) : ℂ) ^ (s' - 1 / 2))⁻¹)
    simp only [← mul_assoc, inv_mul_cancel₀ (hNe s'), one_mul] at h2
    exact h2
  have htrInt : ∀ (i : Fin n) (s' : ℂ),
      ∫ q, fd i s' (Quotient.out q) ∂(unipotentQuotientMeasure ℚ) =
        (((finiteConductor K μ SK) : ℝ) : ℂ) ^ (s' - 1 / 2) * ∫ q, fd' i s' (Quotient.out q) ∂(unipotentQuotientMeasure ℚ) := fun i s' => by
    rw [← (hQT (fd i s') (hfdN i s')).1]
    simp_rw [htr]
    exact MeasureTheory.integral_const_mul _ _

  have hd7 : ∀ (i : Fin n) (s' : ℂ), σd7 i < s'.re →
      ∫ q, fd' i s' (Quotient.out q) ∂(unipotentQuotientMeasure ℚ) =
        RSCarrier.rsArchIntegral RSCarrier.archMeasure μNArch s' (WAd i) (FAd i) *
          RSCarrier.rsFinIntegral μf μNFin s' (fun g => Wfd i (g * hμf)) (fun g => Ffd i (g * hμf)) :=
    fun i s' hs' =>
      LanglandsTunnell.Converse.integral_unipotentQuotient_eq_rsArchIntegral_mul_rsFinIntegral_of_integrable μf μNArch μNFin
        hsplit hNsplit s' (WAd i) (FAd i) (fun g => Wfd i (g * hμf)) (fun g => Ffd i (g * hμf)) (fd' i s') (hfdprod' i s')
        (hfdm' i s') (hfdN' i s') Quotient.out (fun q => Quotient.out_eq' q) (hintd7' i s' hs')
  have hfinIdd : ∀ (i : Fin n) (s' : ℂ), RSCarrier.rsFinIntegral μf μNFin s' (fun g => Wfd i (g * hμf)) (fun g => Ffd i (g * hμf)) =
      RSCarrier.rsFinIntegral μf μNFin s' (fun g => (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor g))
        (fun g => (fun g => Ffd i (g * hμf)) (RSCarrier.finFactor g)) := by
    intro i s'
    simp only [hcoe]
  have hbomd : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      (Φ.b p)⁻¹ = (Ideal.absNorm p.asIdeal : ℂ) * ((Φ.b p)⁻¹ / (Ideal.absNorm p.asIdeal : ℂ)) := by
    intro p _
    have hN0 : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact p.ne_bot)
    rw [mul_div_cancel₀ _ hN0]

  have hψlocd : (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ∀ r : p.adicCompletionIntegers ℚ,
      psiLoc ψ p (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) r) = 1) ∧
    (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ∃ r : p.adicCompletionIntegers ℚ,
      psiLoc ψ p (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) r /
        algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) ≠ 1) :=
    supply_psi_of_inv_eq_psiQ SQ ψ hψQ ϖ hπ hϖ

  have h126d : ∀ (i : Fin n) (s' : ℂ), 1 < (s' + 1 / 2).re →
      (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
        (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor
            ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ)) *
          (fun g => Ffd i (g * hμf)) (RSCarrier.finFactor
            ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ)) =
        (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)) *
          (fun g => Ffd i (g * hμf)) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))) → MeasureTheory.Integrable
      (fun g : finiteAdelicGL2Subgroup ℚ =>
        ((fun g => Wfd i (g * hμf)) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)) * (fun g => Ffd i (g * hμf)) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))) *
        ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s' - 1 / 2))
      (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) →
      RSCarrier.rsFinIntegral μf μNFin s' (fun g => (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor g))
          (fun g => (fun g => Ffd i (g * hμf)) (RSCarrier.finFactor g)) =
        (rsDatum ℚ SQ (fun p => Φ.a p / Φ.b p) (fun p => (Φ.b p)⁻¹)
        (fun 𝔓 => ((fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) 𝔓)⁻¹)
        (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
        (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
        (fun w hw => (archOfParamC K P w hw).dual)
        (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))
        (twistedGammaR K (archOfParamR K P) uR aR)
        (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)).LFun (s' + 1 / 2) *
          RSCarrier.rsFinIntegral μf μNFin s'
            ({g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
            ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
              ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))))
            ({g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
            ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
              ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => (fun g => Ffd i (g * hμf)) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)))) :=
    fun i s' hs hFi hsI =>
      LanglandsTunnell.RankinSelberg.rsFinIntegral_eq_LFun_rsDatum_mul_rsFinIntegral_indicator
        SQ _ _ _ _ _ _ _ s' hconvd hs μf μNFin (fun g => (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor g))
        (fun g => (fun g => Ffd i (g * hμf)) (RSCarrier.finFactor g)) hFi hsI
        (fun p => psiLoc ψ p) ϖ hπ hϖ (fun p => 𝓞 ℚ ⧸ p.asIdeal)
        (fun p x => algebraMap (𝓞 ℚ) (p.adicCompletionIntegers ℚ) (Quotient.out x)) hIcard
        (fun p => (Φ.b p)⁻¹ / (Ideal.absNorm p.asIdeal : ℂ)) hbomd hψlocd.1 hψlocd.2
        (hHLd i).1 (hHLd i).2.1 (hHLd i).2.2.1 (hHLd i).2.2.2
        hHd (fun p _ => hhd0 p) (fun p _ => hhd1 p) (fun p _ => hhd2 p) (fun p _ => hhd3 p)
        uHd (fun p _ => hud0 p) (fun p _ => hud1 p) uZd (fun p _ => huZdoff p) (fun p _ => huZdcone p)
        (hTTd i).1 (hTTd i).2

  have hTD : ∀ s : ℂ, (rsDatum ℚ SQ Φ.a Φ.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        (twistedGammaR K (archOfParamR K P) uR aR)
        (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
        (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
        (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
        (fun w hw => (archOfParamC K P w hw).dual)
        (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).LFunDual s = (rsDatum ℚ SQ (fun p => Φ.a p / Φ.b p) (fun p => (Φ.b p)⁻¹)
        (fun 𝔓 => ((fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) 𝔓)⁻¹)
        (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
        (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
        (fun w hw => (archOfParamC K P w hw).dual)
        (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))
        (twistedGammaR K (archOfParamR K P) uR aR)
        (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)).LFun s :=
    fun _ => rfl

  have hCONTd : ∀ Λ : ℂ → ℂ, Differentiable ℂ Λ →
      (∃ σc : ℝ, ∀ s : ℂ, σc < s.re → Λ s = (pinnedRootNumber K (formalBaseChange ℚ K Φ) μ SK (archOfParamR K P) (archOfParamC K P)
        uR aR uC kC) *
        (((finiteConductor K μ SK) : ℝ) : ℂ) ^ (s - 1 / 2) *
        (fun t : ℂ => ∏ w : ↥SK,
        LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar (ω * μ) w.1) *
        LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar μ w.1) *
        (((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - t)) ^
        (-(LanglandsTunnell.Converse.pinnedExp K (ω * μ) w.1 + LanglandsTunnell.Converse.pinnedExp K μ w.1))) s *
        (rsDatum ℚ SQ Φ.a Φ.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        (twistedGammaR K (archOfParamR K P) uR aR)
        (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
        (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
        (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
        (fun w hw => (archOfParamC K P w hw).dual)
        (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).archFactorDual s *
        (rsDatum ℚ SQ Φ.a Φ.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        (twistedGammaR K (archOfParamR K P) uR aR)
        (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
        (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
        (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
        (fun w hw => (archOfParamC K P w hw).dual)
        (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).LFunDual s) →
      ∀ s : ℂ, 1 < s.re → Λ s = (pinnedRootNumber K (formalBaseChange ℚ K Φ) μ SK (archOfParamR K P) (archOfParamC K P)
        uR aR uC kC) *
        (((finiteConductor K μ SK) : ℝ) : ℂ) ^ (s - 1 / 2) *
        (fun t : ℂ => ∏ w : ↥SK,
        LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar (ω * μ) w.1) *
        LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar μ w.1) *
        (((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - t)) ^
        (-(LanglandsTunnell.Converse.pinnedExp K (ω * μ) w.1 + LanglandsTunnell.Converse.pinnedExp K μ w.1))) s *
        (rsDatum ℚ SQ Φ.a Φ.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        (twistedGammaR K (archOfParamR K P) uR aR)
        (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
        (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
        (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
        (fun w hw => (archOfParamC K P w hw).dual)
        (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).archFactorDual s *
        (rsDatum ℚ SQ Φ.a Φ.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        (twistedGammaR K (archOfParamR K P) uR aR)
        (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
        (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
        (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
        (fun w hw => (archOfParamC K P w hw).dual)
        (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).LFunDual s :=
    fun Λ hΛ hev s hs =>
      eq_mul_archFactorDual_mul_LFunDual_of_eventually _ hwf hLhold (fun s : ℂ => (pinnedRootNumber K (formalBaseChange ℚ K Φ) μ SK (archOfParamR K P) (archOfParamC K P)
        uR aR uC kC) *
        (((finiteConductor K μ SK) : ℝ) : ℂ) ^ (s - 1 / 2) *
        (fun t : ℂ => ∏ w : ↥SK,
        LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar (ω * μ) w.1) *
        LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar μ w.1) *
        (((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - t)) ^
        (-(LanglandsTunnell.Converse.pinnedExp K (ω * μ) w.1 + LanglandsTunnell.Converse.pinnedExp K μ w.1))) s) hEd Λ hΛ hev s hs

  choose σd0 hJ3df using hJ3df
  obtain ⟨M, hM⟩ := Finite.exists_le (fun i : Fin n =>
    max (σd0 i) (σd7 i))
  have hdiffd : Differentiable ℂ (fun s : ℂ => c⁻¹ * ∑ i, coef i *
      rsGlobalIntegral Dm (s + 1 / 2) (fun g => φ i (transposeInvN (Fin 2) g))
        (dualForm (Θ i))) := by
    have heq : (fun s : ℂ => c⁻¹ * ∑ i, coef i *
        rsGlobalIntegral Dm (s + 1 / 2) (fun g => φ i (transposeInvN (Fin 2) g))
          (dualForm (Θ i))) =
        fun s : ℂ => c⁻¹ * ∑ i, coef i * rsGlobalIntegral Dm ((1 - s) - 1 / 2) (φ i) (Θ i) := by
      funext s
      rw [hfe (1 - s)]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      ring
    rw [heq]
    exact hdiff.comp ((differentiable_const (1 : ℂ)).sub differentiable_id)
  refine hCONTd _ hdiffd ⟨max (max M σb) 1 + 1, fun s hs => ?_⟩
  have hsM : M + 1 / 2 < s.re - 1 / 2 := by linarith [le_max_left (max M σb) 1, le_max_left M σb]
  have hsb : σb < s.re := by linarith [le_max_left (max M σb) 1, le_max_right M σb]
  have hs1 : 1 < s.re := by linarith [le_max_right (max M σb) 1]
  have hre : (s - 1 / 2 : ℂ).re = s.re - 1 / 2 := by
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re, Complex.re_ofNat, Complex.normSq_ofNat,
      Complex.one_im, Complex.im_ofNat, mul_zero, zero_div, add_zero]
    norm_num
  have hmemd : ∀ i, rsGlobalIntegral Dm (s + 1 / 2) (fun g => φ i (transposeInvN (Fin 2) g))
        (dualForm (Θ i)) =
      c * (RSCarrier.rsArchIntegral RSCarrier.archMeasure μNArch (s - 1 / 2) (WAd i) (FAd i) *
        ((rsDatum ℚ SQ (fun p => Φ.a p / Φ.b p) (fun p => (Φ.b p)⁻¹)
      (fun 𝔓 => ((fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) 𝔓)⁻¹)
      (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
      (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
      (fun w hw => (archOfParamC K P w hw).dual)
      (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))
      (twistedGammaR K (archOfParamR K P) uR aR)
      (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)).LFun s * ((((finiteConductor K μ SK) : ℝ) : ℂ) ^ (s - 1 / 2 - 1 / 2) * κd i (s - 1 / 2)))) := by
    intro i
    have hMi := hM i
    simp only [max_le_iff] at hMi
    obtain ⟨h0, h7i⟩ := hMi

    rcases Ws23FI.finInvariant_or_rsArchIntegral_eq_zero RSCarrier.archMeasure μNArch (s - 1 / 2) (WAd i) (FAd i) (fun g => Wfd i (g * hμf))
        (fun g => Ffd i (g * hμf)) (fd' i (s - 1 / 2)) (hfdprod' i _) (hfdN' i _) with hFinvB | hA0
    swap
    · rw [hRS, hJ3df i (s - 1 / 2) (by rw [hre]; linarith), htrInt, hd7 _ _ (by rw [hre]; linarith), hA0]
      simp only [zero_mul, mul_zero]
    have hFi : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
        (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor
            ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ)) *
          (fun g => Ffd i (g * hμf)) (RSCarrier.finFactor
            ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ)) =
        (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)) *
          (fun g => Ffd i (g * hμf)) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)) := fun n g => by
      simpa only [hcoe] using hFinvB n g

    rcases LanglandsTunnell.Converse.integrable_rsFinIntegrand_or_rsArchIntegral_eq_zero_of_integrable μf μNArch μNFin
        hsplit hNsplit (s - 1 / 2) (WAd i) (FAd i) (fun g => Wfd i (g * hμf)) (fun g => Ffd i (g * hμf)) (fd' i (s - 1 / 2)) (hfdprod' i _) (hfdm' i _) (hfdN' i _)
        Quotient.out (fun q => Quotient.out_eq' q) (hintd7' i _ (by rw [hre]; linarith)) with hFint | hA0
    · rw [hRS, hJ3df i (s - 1 / 2) (by rw [hre]; linarith), htrInt, hd7 _ _ (by rw [hre]; linarith), hfinIdd,
        h126d _ _ (by rw [sub_add_cancel]; exact hs1) hFi (by simpa only [hcoe] using hFint),
        hJ5ad i _ (by rw [hre]; linarith [le_max_left (max M σb) 1, le_max_right M σb]), sub_add_cancel]
      ring
    · rw [hRS, hJ3df i (s - 1 / 2) (by rw [hre]; linarith), htrInt, hd7 _ _ (by rw [hre]; linarith), hA0]
      simp only [zero_mul, mul_zero]
  have hsumd : ∀ i, coef i * rsGlobalIntegral Dm (s + 1 / 2) (fun g => φ i (transposeInvN (Fin 2) g))
        (dualForm (Θ i)) =
      c * (((rsDatum ℚ SQ (fun p => Φ.a p / Φ.b p) (fun p => (Φ.b p)⁻¹)
      (fun 𝔓 => ((fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) 𝔓)⁻¹)
      (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
      (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
      (fun w hw => (archOfParamC K P w hw).dual)
      (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))
      (twistedGammaR K (archOfParamR K P) uR aR)
      (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)).LFun s * (((finiteConductor K μ SK) : ℝ) : ℂ) ^ (s - 1 / 2 - 1 / 2)) * (coef i *
        (RSCarrier.rsArchIntegral RSCarrier.archMeasure μNArch (s - 1 / 2) (WAd i) (FAd i) *
          κd i (s - 1 / 2)))) := by
    intro i
    rw [hmemd i]
    ring
  show c⁻¹ * ∑ i, coef i * rsGlobalIntegral Dm (s + 1 / 2) (fun g => φ i (transposeInvN (Fin 2) g))
      (dualForm (Θ i)) = _
  simp only [hsumd]
  rw [← Finset.mul_sum, ← Finset.mul_sum, inv_mul_cancel_left₀ hc0, hJ5bd s hsb, hTD s]

  have hNsplit : (((finiteConductor K μ SK) : ℝ) : ℂ) ^ (s - 1 / 2) =
      (((finiteConductor K μ SK) : ℝ) : ℂ) ^ (s - 1 / 2 - 1 / 2) * (((finiteConductor K μ SK) : ℝ) : ℂ) ^ ((1 : ℂ) / 2) := by
    rw [← Complex.cpow_add _ _ hN0]
    congr 1
    ring
  rw [hNsplit]
  ring

#print axioms solution

end S_LanglandsTunnell_RankinSelberg_EntirePairAssembly_dual_identity_family
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_EntirePairAssembly_dual_identity_family (solution)
