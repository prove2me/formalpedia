-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_rsGlobalIntegral_eq_mul_rsArchIntegral_mul_rsFinIntegral_mul_lFun
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ffcbeed9-1fb3-5c65-b3f5-8f59c25b37ab

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Theorems.Thm_LanglandsTunnell_RankinSelberg_rsFinIntegral_eq_LFun_rsDatum_mul_rsFinIntegral_indicator
import Theorems.Thm_LanglandsTunnell_Converse_integral_unipotentQuotient_eq_rsArchIntegral_mul_rsFinIntegral_of_integrable
import Theorems.Thm_LanglandsTunnell_Converse_integrable_rsFinIntegrand_or_rsArchIntegral_eq_zero_of_integrable
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiV
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_rsGlobalIntegral_eq_mul_rsArchIntegral_mul_rsFinIntegral_mul_lFun
p2m_attr_erase "instance" "instCountableOfNumberField_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_rsGlobalIntegral_eq_mul_rsArchIntegral_mul_rsFinIntegral_mul_lFun.LanglandsTunnell LanglandsTunnell.Converse"
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
p2m_open "LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_rsGlobalIntegral_eq_mul_rsArchIntegral_mul_rsFinIntegral_mul_lFun.LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory"
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
p2m_open "NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_rsGlobalIntegral_eq_mul_rsArchIntegral_mul_rsFinIntegral_mul_lFun.LanglandsTunnell LanglandsTunnell.Converse"

section DetNormSplitting

open IsDedekindDomain NumberField Matrix AutomorphicForm
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_rsGlobalIntegral_eq_mul_rsArchIntegral_mul_rsFinIntegral_mul_lFun.LanglandsTunnell LanglandsTunnell.CubicInduction"
open NumberField.AdelicLevel NumberField.AdelicVolume

noncomputable section

namespace DetNormSplit

private abbrev AdGL2 : Type := AdelicGL2 (𝓞 ℚ) ℚ

private theorem coe_finFactor (g : AdGL2) :
    (RSCarrier.finFactor g : AdGL2) =
      (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g))⁻¹ * g := rfl

private theorem glArch_archRealGLAt_ratArchGL2 (g : AdGL2) :
    glArch (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g)) =
      glArch (𝓞 ℚ) ℚ g := by
  have h := (RSCarrier.finFactor g).2
  rw [mem_finiteAdelicGL2Subgroup_iff, coe_finFactor, map_mul, map_inv, inv_mul_eq_one] at h
  exact h

private theorem glFin_archRealGLAt (m : GL (Fin 2) ℝ) :
    glFin (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m) = 1 :=
  glFin_adelicArchGLIncl ℚ _

private theorem abs_det_ratArchGL2 (g : AdGL2) :
    |(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| = archDetNorm (default : InfinitePlace ℚ) g := by
  unfold archDetNorm LanglandsTunnell.ratArchGL2
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  have hcoe : ((Matrix.GeneralLinearGroup.map
      (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).toRingHom
        (archComponent ℚ default (glArch (𝓞 ℚ) ℚ g)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace
          ℚ))).toRingHom.mapMatrix
        ((archComponent ℚ default (glArch (𝓞 ℚ) ℚ g) : GL (Fin 2) (default : InfinitePlace ℚ).Completion) :
          Matrix (Fin 2) (Fin 2) (default : InfinitePlace ℚ).Completion) := rfl
  rw [hcoe, ← RingHom.map_det, ← Real.norm_eq_abs]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).norm_map_of_map_zero (map_zero _) _

private theorem detNorm_eq_archAbs_mul_finNorm (g : AdGL2) :
    detNorm g = |(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| *
      TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (RSCarrier.finFactor g : AdGL2)) := by
  have hg : archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g) *
      (RSCarrier.finFactor g : AdGL2) = g := by
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

private theorem detNorm_cpow_eq_archAbs_cpow_mul_finNorm_cpow (g : AdGL2) (z : ℂ) :
    ((detNorm g : ℝ) : ℂ) ^ z =
      (((|(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| : ℝ) : ℂ) ^ z) *
        ((TateGlobal.ideleNorm ℚ
          (Matrix.GeneralLinearGroup.det (RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ z) := by
  rw [detNorm_eq_archAbs_mul_finNorm, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (NumberField.TateGlobal.ideleNorm_pos _).le]

end DetNormSplit

end

end DetNormSplitting

section FiniteInvarianceSection

p2m_open "IsDedekindDomain NumberField Matrix AutomorphicForm LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_rsGlobalIntegral_eq_mul_rsArchIntegral_mul_rsFinIntegral_mul_lFun.LanglandsTunnell"
open NumberField.AdelicLevel MeasureTheory

noncomputable section

namespace FiniteInvariance

private theorem ratArchGL2_mul (g k : AdelicGL2 (𝓞 ℚ) ℚ) : ratArchGL2 (g * k) = ratArchGL2 g * ratArchGL2 k := by
  unfold LanglandsTunnell.ratArchGL2
  rw [map_mul, map_mul, map_mul]

private theorem ratArchGL2_coe (k : finiteAdelicGL2Subgroup ℚ) : ratArchGL2 (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [(mem_finiteAdelicGL2Subgroup_iff ℚ _).1 k.2, map_one, map_one]

private theorem ratArchGL2_eq_archRealProjAt (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ratArchGL2 g = archRealProjAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) g := by
  ext i j
  rfl

private theorem ratArchGL2_archRealGLAt (m : GL (Fin 2) ℝ) :
    ratArchGL2 (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m) = m := by
  rw [ratArchGL2_eq_archRealProjAt, archRealProjAt_archRealGLAt]

private theorem finFactor_archRealGLAt_mul_coe (m : GL (Fin 2) ℝ) (k : finiteAdelicGL2Subgroup ℚ) :
    RSCarrier.finFactor (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m * k) = k := by
  apply Subtype.ext
  show (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ))
      (ratArchGL2 (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m * ↑k)))⁻¹ *
        (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m * ↑k) = ↑k
  rw [ratArchGL2_mul, ratArchGL2_coe, mul_one, ratArchGL2_archRealGLAt, inv_mul_cancel_left]

private theorem finInvariant_or_arch_eq_zero (A : GL (Fin 2) ℝ → ℂ) (B : finiteAdelicGL2Subgroup ℚ → ℂ)
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
      archRealGLAt_mul_comm_of_glArch_eq_one _ m ((mem_finiteAdelicGL2Subgroup_iff ℚ _).1 (n :
          finiteAdelicGL2Subgroup ℚ).2)
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

private theorem rsArchIntegral_eq_zero_of_forall_eq_zero [MeasurableSpace (GL (Fin 2) ℝ)] (μ : Measure (GL (Fin 2) ℝ))
    (μN : Measure RSCarrier.realUnipotent) (s : ℂ) (W F : GL (Fin 2) ℝ → ℂ)
    (h : ∀ m : GL (Fin 2) ℝ,
      (W m * F m) * (((|(Matrix.GeneralLinearGroup.det m : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)) = 0) :
    RSCarrier.rsArchIntegral μ μN s W F = 0 := by
  unfold RSCarrier.rsArchIntegral RSCarrier.rsLocalIntegral
  simp only [h, integral_zero]

private theorem det_coe_finUnipotent_mul (n : RSCarrier.finUnipotent) (k : finiteAdelicGL2Subgroup ℚ) :
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

private theorem finInvariant_or_rsArchIntegral_eq_zero [MeasurableSpace (GL (Fin 2) ℝ)] (μ : Measure (GL (Fin 2) ℝ))
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
    have hne : ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2))
        ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      exact Or.inl (Complex.ofReal_ne_zero.2 (TateGlobal.ideleNorm_pos _).ne')
    exact mul_right_cancel₀ hne h
  · exact Or.inr (rsArchIntegral_eq_zero_of_forall_eq_zero μ μN s WA FA hA)

end FiniteInvariance

end

end FiniteInvarianceSection

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam CubicInduction.psiLoc ratArchGL2 RankinSelberg.rsFinIntegral_eq_LFun_rsDatum_mul_rsFinIntegral_indicator Converse.integral_unipotentQuotient_eq_rsArchIntegral_mul_rsFinIntegral_of_integrable Converse.integrable_rsFinIntegrand_or_rsArchIntegral_eq_zero_of_integrable TateLocal.addCharLevel_psiLocal_rat TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel TateLocal.psiLocal_ne_one"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "inducedE1 inducedE2 inducedE3 rsDatum rsGlobalIntegral rsFinIntegral_eq_LFun_rsDatum_mul_rsFinIntegral_indicator"
namespace MemberFactorisation
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

open LanglandsTunnell.CubicInduction AutomorphicForm MeasureTheory

private theorem finFactor_coe (g : finiteAdelicGL2Subgroup ℚ) : RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) = g := by
  apply Subtype.ext
  have h1 : ratArchGL2 (g : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
    unfold LanglandsTunnell.ratArchGL2
    rw [(mem_finiteAdelicGL2Subgroup_iff ℚ _).1 g.2, map_one, map_one]
  simp only [RSCarrier.finFactor, h1, map_one, inv_one, one_mul]

private theorem _root_.LanglandsTunnell.RankinSelberg.MemberFactorisation.detNorm_cpow_eq_archAbs_cpow_mul_finNorm_cpow (g : AdelicGL2 (𝓞 ℚ) ℚ) (z : ℂ) :
    ((detNorm g : ℝ) : ℂ) ^ z =
      (((|(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| : ℝ) : ℂ) ^ z) *
        ((TateGlobal.ideleNorm ℚ
          (Matrix.GeneralLinearGroup.det (RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ z) :=
  DetNormSplit.detNorm_cpow_eq_archAbs_cpow_mul_finNorm_cpow g z

p2m_export "LanglandsTunnell.RankinSelberg.MemberFactorisation" "detNorm_cpow_eq_archAbs_cpow_mul_finNorm_cpow"
section psi_level
open IsDedekindDomain NumberField
private theorem uniformizer_valuation_facts (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∃ ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
        algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0) ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
        Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ)) := by
  refine ⟨fun p => ⟨(AdelicLevel.uniformizerUnit ℚ p : (p.adicCompletion ℚ)ˣ), ?_⟩, ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, AdelicLevel.valued_uniformizerUnit]
    exact le_of_lt (WithZero.exp_lt_exp.2 (by norm_num))
  · intro p _
    exact (AdelicLevel.uniformizerUnit ℚ p).ne_zero
  · intro p _
    exact AdelicLevel.valued_uniformizerUnit ℚ p

private theorem psiLoc_psiQ_eq_psiV (v : HeightOneSpectrum (𝓞 ℚ)) :
    LanglandsTunnell.CubicInduction.psiLoc NumberField.StandardAddChar.psiQ v = NumberField.StandardAddChar.psiV v
        := by
  classical
  refine DFunLike.ext _ _ fun x => ?_
  show NumberField.StandardAddChar.psiQ (NumberField.StandardAddChar.adeleSingleAt ℚ v x) = _
  rw [show NumberField.StandardAddChar.adeleSingleAt ℚ v x =
      ((0 : InfiniteAdeleRing ℚ), NumberField.StandardAddChar.finAdeleSingleAt ℚ v x) from rfl,
    NumberField.StandardAddChar.psiQ_apply]
  simp only
  rw [AddChar.map_zero_eq_one, one_mul, NumberField.StandardAddChar.psiFin_apply]
  rw [finprod_eq_single (fun w => NumberField.StandardAddChar.psiV w (NumberField.StandardAddChar.finAdeleSingleAt
      ℚ v x w)) v]
  · rw [NumberField.StandardAddChar.finAdeleSingleAt_apply_self]
  · intro w hw
    rw [NumberField.StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ v x hw]
    exact AddChar.map_zero_eq_one _

private theorem psiLoc_psiQ_eq_psiLocal (v : HeightOneSpectrum (𝓞 ℚ)) :
    LanglandsTunnell.CubicInduction.psiLoc NumberField.StandardAddChar.psiQ v =
        NumberField.StandardAddChar.psiLocal ℚ v := by
  rw [psiLoc_psiQ_eq_psiV, NumberField.StandardAddChar.psiLocal_rat_eq_psiV]

private theorem psiQ_level_facts (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
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

end psi_level

end LanglandsTunnell.RankinSelberg.MemberFactorisation

open LanglandsTunnell.RankinSelberg.MemberFactorisation in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ) (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (P : RealArchParam)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (_hunr : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ¬ IsRamifiedIn K p)
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)] [hIfin : ∀ p : HeightOneSpectrum (𝓞 ℚ), Fintype (𝓞 ℚ ⧸ p.asIdeal)]
    (Dm : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (c : ℂ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (μf : MeasureTheory.Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
    (μNFin : MeasureTheory.Measure RSCarrier.finUnipotent) [μNFin.IsHaarMeasure]
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ))
    {n : ℕ} (φ : Fin n → AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Θ W : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (μNArch : MeasureTheory.Measure RSCarrier.realUnipotent) [μNArch.IsHaarMeasure]
      (_hsplit : MeasureTheory.Measure.map (fun g : AdelicGL2 (𝓞 ℚ) ℚ => (ratArchGL2 g, RSCarrier.finFactor g))
        (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) = RSCarrier.archMeasure.prod μf)
      (_hNsplit : MeasureTheory.Measure.map
        (fun n : adelicUnipotent ℚ => (ratArchGL2 (n : AdelicGL2 (𝓞 ℚ) ℚ), RSCarrier.finFactor n))
        (unipotentHaar ℚ) =
        (MeasureTheory.Measure.map Subtype.val μNArch).prod (MeasureTheory.Measure.map Subtype.val μNFin))
      (_hconv : (rsDatum ℚ SQ Φ.a Φ.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          (twistedGammaR K (archOfParamR K P) uR aR)
          (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
          (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
          (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
          (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).Converges)
      (_hwf : (rsDatum ℚ SQ Φ.a Φ.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          (twistedGammaR K (archOfParamR K P) uR aR)
          (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
          (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
          (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
          (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).WellFormed)
      (WA : Fin n → GL (Fin 2) ℝ → ℂ) (Wf : Fin n → finiteAdelicGL2Subgroup ℚ → ℂ)
      (_hWAf : ∀ (i : Fin n) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ
            N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
                NumberField.StandardAddChar.psiQ (φ i) 1 g =
          WA i (ratArchGL2 g) * Wf i (RSCarrier.finFactor g))
      (_hHL : ∀ i : Fin n,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ∀ (x : p.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf i (RSCarrier.finFactor (UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.unipotent x) * g)) =
            psiLoc NumberField.StandardAddChar.psiQ p x * Wf i (RSCarrier.finFactor g)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
          ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
            x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
              Wf i (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p x)) = Wf i (RSCarrier.finFactor g)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ hp : p ∉ SQ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          (∑ r, Wf i (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.repSome
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp)
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ)
                (algebraMap (𝓞 ℚ) (p.adicCompletionIntegers ℚ) (Quotient.out (r : 𝓞 ℚ ⧸ p.asIdeal)))))))) +
            Wf i (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.repInf
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp)))) =
            Φ.a p * Wf i (RSCarrier.finFactor g)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ hp : p ∉ SQ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          Wf i (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.scalarPi
            (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp)))) =
            (Φ.b p / (Ideal.absNorm p.asIdeal : ℂ)) * Wf i (RSCarrier.finFactor g)))
      (FA : Fin n → GL (Fin 2) ℝ → ℂ) (Ff : Fin n → finiteAdelicGL2Subgroup ℚ → ℂ)
      (_hFAf : ∀ (i : Fin n) (g : AdelicGL2 (𝓞 ℚ) ℚ), W i (iota (𝓞 ℚ) ℚ g) = FA i (ratArchGL2 g) * Ff i
          (RSCarrier.finFactor g))
      (hH : HeightOneSpectrum (𝓞 ℚ) → ℕ → ℂ)
      (_hHrec : (∀ p, hH p 0 = 1) ∧ (∀ p, hH p 1 = inducedE1 ℚ (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ
          (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) p) ∧
        (∀ p, hH p 2 = inducedE1 ℚ (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else
            0) p ^ 2 - inducedE2 ℚ (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else
                0) p) ∧
        (∀ p (n : ℕ), hH p (n + 3) = inducedE1 ℚ (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) :
            ℂˣ) : ℂ) else 0) p * hH p (n + 2) - inducedE2 ℚ (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ
                (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) p * hH p (n + 1) +
          inducedE3 ℚ (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) p * hH p
              n))
      (uH : HeightOneSpectrum (𝓞 ℚ) → ℕ → ℕ → ℂ)
      (_uHrec : (∀ p k, uH p k 0 = hH p k) ∧
        (∀ p k₁ k₂, uH p k₁ (k₂ + 1) = hH p k₁ * hH p (k₂ + 1) - hH p (k₁ + 1) * hH p k₂))
      (uZ : HeightOneSpectrum (𝓞 ℚ) → ℤ → ℤ → ℂ)
      (_uZrec : (∀ p (m₁ m₂ : ℤ), (m₂ < 0 ∨ m₁ < m₂) → uZ p m₁ m₂ = 0) ∧
        (∀ p (k₁ k₂ : ℕ), k₂ ≤ k₁ → uZ p k₁ k₂ = uH p k₁ k₂))
      (_hTT : ∀ i : Fin n,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
          ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
            x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
              Ff i (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p x)) = Ff i (RSCarrier.finFactor g)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ hp : p ∉ SQ, ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (m₁ m₂ : ℤ),
          localAt ℚ p g = 1 →
            Ff i (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p
                (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p
                    hp) (m₁ - m₂) *
                  UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ
                      p hp) ^ m₂))) =
              Ff i (RSCarrier.finFactor g) * ((Ideal.absNorm p.asIdeal : ℂ)⁻¹ ^ m₁ * uZ p m₁ m₂)))
      (f : Fin n → ℂ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
      (_hf : ∀ i s' g, f i s' g =
        whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ
            N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ⁻¹ (φ i) 1 g * W i
                (iota (𝓞 ℚ) ℚ g) *
          ((detNorm g : ℝ) : ℂ) ^ (s' - 1 / 2))
      (_hJ3f : ∀ i, ∃ σ0 : ℝ, ∀ s' : ℂ, σ0 < s'.re →
        rsGlobalIntegral Dm s' (φ i) (Θ i) = c * ∫ q, f i s' (Quotient.out q) ∂(unipotentQuotientMeasure ℚ))
      (_hfm : ∀ (i : Fin n) (s' : ℂ), Measurable (f i s'))
      (_hfN : ∀ (i : Fin n) (s' : ℂ) (u : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        f i s' ((u : AdelicGL2 (𝓞 ℚ) ℚ) * g) = f i s' g)
      (_hint7 : ∀ i : Fin n, ∃ σ7 : ℝ, ∀ s' : ℂ, σ7 < s'.re →
        MeasureTheory.Integrable (fun q : UnipotentQuotient ℚ => f i s' (Quotient.out q)) (unipotentQuotientMeasure
            ℚ)),
    ∀ i : Fin n, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      rsGlobalIntegral Dm (s - 1 / 2) (φ i) (Θ i) =
        c * RSCarrier.rsArchIntegral RSCarrier.archMeasure μNArch (s - 1 / 2) (WA i) (FA i) *
        RSCarrier.rsFinIntegral μf μNFin (s - 1 / 2)
          ({g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => Wf i (RSCarrier.finFactor (g :
                      AdelicGL2 (𝓞 ℚ) ℚ))))
          ({g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => Ff i (RSCarrier.finFactor (g :
                      AdelicGL2 (𝓞 ℚ) ℚ)))) *
        (rsDatum ℚ SQ Φ.a Φ.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          (twistedGammaR K (archOfParamR K P) uR aR)
          (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
          (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
          (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
          (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).LFun s := by
  intro μNArch _ hsplit hNsplit hconv _ WA Wf hWAf hHL FA Ff hFAf hH hHrec uH uHrec uZ uZrec hTT f hf hJ3f hfm hfN
    hint7 i
  obtain ⟨hh0, hh1, hh2, hh3⟩ := hHrec
  obtain ⟨hu0, hu1⟩ := uHrec
  obtain ⟨huZoff, huZcone⟩ := uZrec
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
  have hbom : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Φ.b p = (Ideal.absNorm p.asIdeal : ℂ) * (Φ.b p / (Ideal.absNorm p.asIdeal : ℂ)) := by
    intro p _
    have hN0 : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact p.ne_bot)
    rw [mul_div_cancel₀ _ hN0]
  have hψloc : (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ∀ r : p.adicCompletionIntegers ℚ,
      psiLoc NumberField.StandardAddChar.psiQ p
        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) r) = 1) ∧
    (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ∃ r : p.adicCompletionIntegers ℚ,
      psiLoc NumberField.StandardAddChar.psiQ p
        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) r /
          algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) ≠ 1) :=
    psiQ_level_facts SQ ϖ hπ hϖ
  have h126 : ∀ (i : Fin n) (s' : ℂ), 1 < (s' + 1 / 2).re →
      (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
        Wf i (RSCarrier.finFactor
            ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ)) *
          Ff i (RSCarrier.finFactor
            ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ)) =
        Wf i (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)) * Ff i (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))) →
            MeasureTheory.Integrable
      (fun g : finiteAdelicGL2Subgroup ℚ =>
        (Wf i (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)) * Ff i (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))) *
        ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s' - 1 / 2))
      (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) →
      RSCarrier.rsFinIntegral μf μNFin s' (fun g => Wf i (RSCarrier.finFactor g))
          (fun g => Ff i (RSCarrier.finFactor g)) =
        (rsDatum ℚ SQ Φ.a Φ.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        (twistedGammaR K (archOfParamR K P) uR aR)
        (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
        (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
        (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
        (fun w hw => (archOfParamC K P w hw).dual)
        (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).LFun (s' + 1 / 2) *
          RSCarrier.rsFinIntegral μf μNFin s'
            ({g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
            ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
              ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => Wf i (RSCarrier.finFactor (g :
                    AdelicGL2 (𝓞 ℚ) ℚ))))
            ({g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
            ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
              ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => Ff i (RSCarrier.finFactor (g :
                    AdelicGL2 (𝓞 ℚ) ℚ)))) :=
    fun i s' hs hFi hsI =>
      LanglandsTunnell.RankinSelberg.rsFinIntegral_eq_LFun_rsDatum_mul_rsFinIntegral_indicator
        SQ _ _ _ _ _ _ _ s' hconv hs μf μNFin (fun g => Wf i (RSCarrier.finFactor g))
        (fun g => Ff i (RSCarrier.finFactor g)) hFi hsI
        (fun p => psiLoc NumberField.StandardAddChar.psiQ p) ϖ hπ hϖ (fun p => 𝓞 ℚ ⧸ p.asIdeal)
        (fun p x => algebraMap (𝓞 ℚ) (p.adicCompletionIntegers ℚ) (Quotient.out x)) hIcard
        (fun p => Φ.b p / (Ideal.absNorm p.asIdeal : ℂ)) hbom hψloc.1 hψloc.2
        (hHL i).1 (hHL i).2.1 (hHL i).2.2.1 (hHL i).2.2.2
        hH (fun p _ => hh0 p) (fun p _ => hh1 p) (fun p _ => hh2 p) (fun p _ => hh3 p)
        uH (fun p _ => hu0 p) (fun p _ => hu1 p) uZ (fun p _ => huZoff p) (fun p _ => huZcone p)
        (hTT i).1 (hTT i).2
  have hfprod : ∀ (i : Fin n) (s' : ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ), f i s' g =
      ((WA i (ratArchGL2 g) * FA i (ratArchGL2 g)) *
          (((|(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| : ℝ) : ℂ) ^ (s' - 1 / 2))) *
        ((Wf i (RSCarrier.finFactor g) * Ff i (RSCarrier.finFactor g)) *
          ((TateGlobal.ideleNorm ℚ
            (Matrix.GeneralLinearGroup.det (RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s' - 1 / 2))) := by
    intro i s' g
    simp only [hf, hψQ, hWAf, hFAf, hdetC]
    ring
  choose σ7 hint7 using hint7
  have h7 : ∀ (i : Fin n) (s' : ℂ), σ7 i < s'.re →
      ∫ q, f i s' (Quotient.out q) ∂(unipotentQuotientMeasure ℚ) =
        RSCarrier.rsArchIntegral RSCarrier.archMeasure μNArch s' (WA i) (FA i) *
          RSCarrier.rsFinIntegral μf μNFin s' (Wf i) (Ff i) :=
    fun i s' hs' =>
      LanglandsTunnell.Converse.integral_unipotentQuotient_eq_rsArchIntegral_mul_rsFinIntegral_of_integrable μf
          μNArch μNFin
        hsplit hNsplit s' (WA i) (FA i) (Wf i) (Ff i) (f i s') (hfprod i s')
        (hfm i s') (hfN i s') Quotient.out (fun q => Quotient.out_eq' q) (hint7 i s' hs')
  have hfinId : ∀ (i : Fin n) (s' : ℂ), RSCarrier.rsFinIntegral μf μNFin s' (Wf i) (Ff i) =
      RSCarrier.rsFinIntegral μf μNFin s' (fun g => Wf i (RSCarrier.finFactor g))
        (fun g => Ff i (RSCarrier.finFactor g)) := by
    intro i s'
    simp only [hcoe]
  choose σ0 hJ3f using hJ3f
  refine ⟨max (max (σ0 i) (σ7 i) + 1 / 2) 1, fun s hs => ?_⟩
  have hre : (s - 1 / 2 : ℂ).re = s.re - 1 / 2 := by
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re, Complex.re_ofNat, Complex.normSq_ofNat,
      Complex.one_im, Complex.im_ofNat, mul_zero, zero_div, add_zero]
    norm_num
  have hmx := le_max_left (max (σ0 i) (σ7 i) + 1 / 2) (1 : ℝ)
  have h0 : σ0 i < (s - 1 / 2 : ℂ).re := by rw [hre]; linarith [le_max_left (σ0 i) (σ7 i)]
  have h7i : σ7 i < (s - 1 / 2 : ℂ).re := by rw [hre]; linarith [le_max_right (σ0 i) (σ7 i)]
  have hs1 : 1 < s.re := by linarith [le_max_right (max (σ0 i) (σ7 i) + 1 / 2) (1 : ℝ)]
  rcases FiniteInvariance.finInvariant_or_rsArchIntegral_eq_zero RSCarrier.archMeasure μNArch (s - 1 / 2) (WA i) (FA i)
      (Wf i) (Ff i) (f i (s - 1 / 2)) (hfprod i _) (hfN i _) with hFinvB | hA0
  swap
  · rw [hJ3f i (s - 1 / 2) h0, h7 _ _ h7i, hA0]
    simp only [zero_mul, mul_zero]
  have hFi : ∀ (m : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      Wf i (RSCarrier.finFactor
          ((((m : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ)) *
        Ff i (RSCarrier.finFactor
          ((((m : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ)) =
      Wf i (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)) * Ff i (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)) :=
    fun m g => by simpa only [hcoe] using hFinvB m g
  rcases LanglandsTunnell.Converse.integrable_rsFinIntegrand_or_rsArchIntegral_eq_zero_of_integrable μf μNArch μNFin
      hsplit hNsplit (s - 1 / 2) (WA i) (FA i) (Wf i) (Ff i) (f i (s - 1 / 2)) (hfprod i _) (hfm i _) (hfN i _)
      Quotient.out (fun q => Quotient.out_eq' q) (hint7 i _ h7i) with hFint | hA0
  · rw [hJ3f i (s - 1 / 2) h0, h7 _ _ h7i, hfinId,
      h126 _ _ (by rw [sub_add_cancel]; exact hs1) hFi (by simpa only [hcoe] using hFint), sub_add_cancel]
    ring
  · rw [hJ3f i (s - 1 / 2) h0, h7 _ _ h7i, hA0]
    simp only [zero_mul, mul_zero]

end S_LanglandsTunnell_RankinSelberg_exists_forall_rsGlobalIntegral_eq_mul_rsArchIntegral_mul_rsFinIntegral_mul_lFun
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_rsGlobalIntegral_eq_mul_rsArchIntegral_mul_rsFinIntegral_mul_lFun (solution)
