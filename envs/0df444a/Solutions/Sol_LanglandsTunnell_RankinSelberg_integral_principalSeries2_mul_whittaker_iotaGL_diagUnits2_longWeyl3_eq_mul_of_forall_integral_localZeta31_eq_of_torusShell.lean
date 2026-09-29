-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.integral_principalSeries2_mul_whittaker_iotaGL_diagUnits2_longWeyl3_eq_mul_of_forall_integral_localZeta31_eq_of_torusShell
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/78e4cb48-c22e-5c9b-8b78-92f08c82dfa6

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Theorems.Thm_LanglandsTunnell_RankinSelberg_integrable_principalSeries2_mul_whittaker_iotaGL_diagUnitGL2_mul_lowerUnipotent21_of_integrable_whittaker_iotaGL_mul_principalSeries2
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_polynomial_localZeta31_iotaGL_eq_and_localZeta30_dualWhittakerFn3_eq_mul_of_forall_mem_gl3CyclicSubspace_fe_of_torusShell
import Theorems.Thm_MeasureTheory_exists_hasSum_mul_zpow_eval_mul_integral_prod_of_ae_forall_integral_mul_zpow_mul_eval_eq
import Theorems.Thm_Complex_eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_integral_principalSeries2_mul_whittaker_iotaGL_diagUnits2_longWeyl3_eq_mul_of_forall_integral_localZeta31_eq_of_torusShell
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction Filter Topology

open scoped ENNReal NNReal Matrix

noncomputable section

namespace KcR5P

section Inst

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

scoped instance borelSpace_units_adic : BorelSpace (HeightOneSpectrum.adicCompletion ℚ p)ˣ := borelSpace_units

scoped instance secondCountable_units_adic : SecondCountableTopology (HeightOneSpectrum.adicCompletion ℚ p)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

scoped instance isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  set c : ℝ≥0 := (Ideal.absNorm p.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ p = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

scoped instance isHaarMeasure_mulHaar :
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (HeightOneSpectrum.adicCompletion ℚ p)ˣ).IsHaarMeasure :=
  isHaarMeasure_comap_val_mulMeasure ℚ p (selfDualHaarAt ℚ p)

theorem one_lt_q : 1 < Ideal.absNorm p.asIdeal := by
  refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot, ?_⟩
  exact Ideal.absNorm_eq_one_iff.not.mpr (Ideal.IsPrime.ne_top p.isPrime)

theorem one_lt_qR : (1 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := by exact_mod_cast one_lt_q p

theorem qR_pos : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := lt_trans zero_lt_one (one_lt_qR p)

theorem qC_ne_zero : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by
  exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot)

theorem qC_eq : (Ideal.absNorm p.asIdeal : ℂ) = ((Ideal.absNorm p.asIdeal : ℝ) : ℂ) := by norm_cast

theorem log_qR_pos : 0 < Real.log (Ideal.absNorm p.asIdeal : ℝ) := Real.log_pos (one_lt_qR p)

theorem log_qC : Complex.log (Ideal.absNorm p.asIdeal : ℂ) = ((Real.log (Ideal.absNorm p.asIdeal : ℝ) : ℝ) : ℂ) := by
  rw [qC_eq, ← Complex.ofReal_log (qR_pos p).le]

theorem qC_cpow_cpow (y z : ℂ) (hy : y.im = 0) :
    ((Ideal.absNorm p.asIdeal : ℂ) ^ y) ^ z = (Ideal.absNorm p.asIdeal : ℂ) ^ (y * z) := by
  have hlog : (Complex.log (Ideal.absNorm p.asIdeal : ℂ)).im = 0 := by rw [log_qC]; exact Complex.ofReal_im _
  rw [Complex.cpow_mul]
  · rw [Complex.mul_im, hlog, hy]; simp [Real.pi_pos]
  · rw [Complex.mul_im, hlog, hy]; simp [Real.pi_pos.le]

theorem norm_qC_cpow_neg (S : ℂ) :
    ‖(Ideal.absNorm p.asIdeal : ℂ) ^ (-S)‖ = (Ideal.absNorm p.asIdeal : ℝ) ^ (-S.re) := by
  rw [qC_eq, Complex.norm_cpow_eq_rpow_re_of_pos (qR_pos p), Complex.neg_re]

theorem norm_qC_cpow (S : ℂ) :
    ‖(Ideal.absNorm p.asIdeal : ℂ) ^ S‖ = (Ideal.absNorm p.asIdeal : ℝ) ^ S.re := by
  rw [qC_eq, Complex.norm_cpow_eq_rpow_re_of_pos (qR_pos p)]

theorem exists_cpow_neg_eq {Y : ℂ} (hY : Y ≠ 0) :
    ∃ S : ℂ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-S) = Y ∧ (Ideal.absNorm p.asIdeal : ℝ) ^ (-S.re) = ‖Y‖ := by
  have hlog0 : ((Real.log (Ideal.absNorm p.asIdeal : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (log_qR_pos p).ne'
  refine ⟨-(Complex.log Y / ((Real.log (Ideal.absNorm p.asIdeal : ℝ) : ℝ) : ℂ)), ?_, ?_⟩
  · rw [neg_neg, Complex.cpow_def_of_ne_zero (qC_ne_zero p), log_qC, mul_div_cancel₀ _ hlog0, Complex.exp_log hY]
  · rw [← norm_qC_cpow_neg, neg_neg, Complex.cpow_def_of_ne_zero (qC_ne_zero p), log_qC, mul_div_cancel₀ _ hlog0,
      Complex.exp_log hY]

theorem norm_lt_rpow_neg_iff (S : ℂ) (σ : ℝ) :
    (Ideal.absNorm p.asIdeal : ℝ) ^ (-S.re) < (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ) ↔ σ < S.re := by
  rw [Real.rpow_lt_rpow_left_iff (one_lt_qR p)]
  constructor <;> intro h <;> linarith

theorem rpow_lt_norm_iff (S : ℂ) (σ : ℝ) :
    (Ideal.absNorm p.asIdeal : ℝ) ^ σ < (Ideal.absNorm p.asIdeal : ℝ) ^ (-S.re) ↔ S.re < -σ := by
  rw [Real.rpow_lt_rpow_left_iff (one_lt_qR p)]
  constructor <;> intro h <;> linarith

end Inst

section Ord

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

def ordU (u : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : ℤ := -WithZero.log (Valued.v (u : F))

variable {p}

theorem valued_eq_exp_neg_ordU (u : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    Valued.v (u : F) = WithZero.exp (-ordU p u) := by
  rw [ordU, neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).mpr u.ne_zero)]

theorem norm_eq_of_valued_eq_exp {m : ℤ} {a : F} (ha : Valued.v a = WithZero.exp m) :
    ‖a‖ = (Ideal.absNorm p.asIdeal : ℝ) ^ m := by
  rw [NumberField.FinitePlace.norm_def, ha, WithZero.exp,
    WithZeroMulInt.toNNReal_neg_apply _ (WithZero.coe_ne_zero), WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow]
  rfl

theorem norm_units_eq (u : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    ‖(u : F)‖ = (Ideal.absNorm p.asIdeal : ℝ) ^ (-ordU p u) :=
  norm_eq_of_valued_eq_exp (valued_eq_exp_neg_ordU u)

theorem coe_modulus_eq_norm (x : F) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem modulus_units_ne_zero (u : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : (((modulus (u : F) : ℝ≥0) : ℝ) : ℂ) ≠ 0 := by
  rw [coe_modulus_eq_norm]
  exact_mod_cast (norm_pos_iff.mpr u.ne_zero).ne'

theorem modulus_cpow (u : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) (S : ℂ) :
    (((modulus (u : F) : ℝ≥0) : ℝ) : ℂ) ^ S = ((Ideal.absNorm p.asIdeal : ℂ) ^ (-S)) ^ (ordU p u) := by
  rw [coe_modulus_eq_norm, norm_units_eq, Complex.ofReal_zpow, ← qC_eq, ← Complex.cpow_intCast, qC_cpow_cpow p _ _ (by simp),
    ← Complex.cpow_int_mul]
  congr 1
  push_cast
  ring

theorem modulus_cpow_sub_one (u : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) (S : ℂ) :
    (((modulus (u : F) : ℝ≥0) : ℝ) : ℂ) ^ (S - 1) =
      (((modulus (u : F) : ℝ≥0) : ℝ) : ℂ)⁻¹ * ((Ideal.absNorm p.asIdeal : ℂ) ^ (-S)) ^ (ordU p u) := by
  rw [Complex.cpow_sub _ _ (modulus_units_ne_zero u), Complex.cpow_one, modulus_cpow, div_eq_inv_mul]

theorem modulus_cpow_neg_sub_one (u : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) (S : ℂ) :
    (((modulus (u : F) : ℝ≥0) : ℝ) : ℂ) ^ (-S - 1) =
      (((modulus (u : F) : ℝ≥0) : ℝ) : ℂ)⁻¹ * ((Ideal.absNorm p.asIdeal : ℂ) ^ S) ^ (ordU p u) := by
  rw [modulus_cpow_sub_one, neg_neg]

theorem measurable_ordU : Measurable (ordU p) := by
  refine measurable_to_countable' fun n => ?_
  have hset : ordU p ⁻¹' {n} = Units.val ⁻¹' Metric.sphere (0 : F) ((Ideal.absNorm p.asIdeal : ℝ) ^ (-n)) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_singleton_iff, mem_sphere_zero_iff_norm]
    constructor
    · intro h
      rw [norm_units_eq, h]
    · intro h
      rw [norm_units_eq] at h
      have hinj := zpow_right_injective₀ (qR_pos p) (one_lt_qR p).ne' h
      have : -ordU p u = -n := hinj
      linarith
  rw [hset]
  exact (Metric.isClosed_sphere.preimage Units.continuous_val).measurableSet

end Ord

section Algebra

variable {A : Type*} [CommRing A]

theorem transposeInv3_coe (g : GL (Fin 3) A) :
    ((transposeInv3 g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ := rfl

theorem transposeInv3_mul (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  rw [Units.val_mul, transposeInv3_coe, transposeInv3_coe, transposeInv3_coe, _root_.mul_inv_rev, Units.val_mul,
    Matrix.transpose_mul]

theorem transposeInv3_transposeInv3 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  show ((((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ)ᵀ = _
  exact Matrix.transpose_transpose _

theorem transposeInv3_iotaGL_diagUnitGL2 (a : Aˣ) :
    transposeInv3 (iotaGL (diagUnitGL2 a) : GL (Fin 3) A) = iotaGL (diagUnitGL2 a⁻¹) := by
  refine Units.ext ?_
  rw [transposeInv3_coe, ← map_inv, coe_iotaGL, coe_iotaGL]
  have : (diagUnitGL2 a)⁻¹ = diagUnitGL2 a⁻¹ := by
    refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
    rw [Units.val_mul, coe_diagUnitGL2, coe_diagUnitGL2, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [this, coe_diagUnitGL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.transpose_apply]

theorem longWeyl3_dual_point (a t : Aˣ) (y : A) :
    (longWeyl3 : GL (Fin 3) A) * (iotaGL (diagUnitGL2 a⁻¹) * (weylPrime3 * iotaGL (diagUnits2 1 t * unipotentGL2 y))) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) a⁻¹ *
        (iotaGL (diagUnits2 (t * a) a) * (longWeyl3 * upperUnipotent3 0 0 y * weylPrime3)) := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_iotaGL, coe_diagUnitGL2, coe_diagUnits2, upperUnipotent3_coe, weylPrime3_coe,
    longWeyl3_coe, map_mul, unipotentGL2_coe, Matrix.GeneralLinearGroup.scalar, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.scalar_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal]
  rw [mul_comm (t : A), ← mul_assoc, Units.inv_mul, one_mul]

theorem dual_point {R : Type*} [Field R] (V : GL (Fin 3) A → R) (ω : Aˣ →* Rˣ)
    (hVω : ∀ (z : Aˣ) (g : GL (Fin 3) A), V (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : Rˣ) : R) * V g)
    (a t : Aˣ) (y : A) :
    dualWhittakerFn3 V (iotaGL (diagUnitGL2 a) * (weylPrime3 * transposeInv3 (iotaGL (diagUnits2 1 t * unipotentGL2 y)))) =
      ((ω a : Rˣ) : R)⁻¹ * V (iotaGL (diagUnits2 (t * a) a) * (longWeyl3 * upperUnipotent3 0 0 y * weylPrime3)) := by
  rw [dualWhittakerFn3_apply, transposeInv3_mul, transposeInv3_mul, transposeInv3_iotaGL_diagUnitGL2,
    transposeInv3_weylPrime3, transposeInv3_transposeInv3, longWeyl3_dual_point, hVω, map_inv, Units.val_inv_eq_inv_val]

end Algebra

section AlgebraLocal

variable {p : HeightOneSpectrum (𝓞 ℚ)}

theorem upperUnipotent2_eq (x : p.adicCompletion ℚ) :
    upperUnipotent2 p x = (unipotentGL2 x : GL (Fin 2) (p.adicCompletion ℚ)) :=
  Units.ext rfl

end AlgebraLocal

section Tools

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

theorem integral_prod_four (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd]
    (H : α × β × γ × δ → ℂ) (hH : Integrable H (μa.prod (μb.prod (μc.prod μd)))) :
    ∫ q, H q ∂(μa.prod (μb.prod (μc.prod μd))) = ∫ a, ∫ b, ∫ c, ∫ d, H (a, b, c, d) ∂μd ∂μc ∂μb ∂μa := by
  rw [integral_prod _ hH]
  refine integral_congr_ae ?_
  filter_upwards [hH.prod_right_ae] with a ha
  rw [integral_prod _ ha]
  refine integral_congr_ae ?_
  filter_upwards [ha.prod_right_ae] with b hb
  rw [integral_prod _ hb]

def laurentCoeff (P : Polynomial ℂ) (m : ℤ) (j : ℤ) : ℂ :=
  if 0 ≤ j + m then P.coeff (j + m).toNat else 0

theorem laurentCoeff_eq_zero_of_not_mem (P : Polynomial ℂ) (m : ℤ) {j : ℤ}
    (hj : j ∉ (Finset.range (P.natDegree + 1)).image (fun i : ℕ => (i : ℤ) - m)) : laurentCoeff P m j = 0 := by
  unfold laurentCoeff
  split_ifs with h
  · apply Polynomial.coeff_eq_zero_of_natDegree_lt
    by_contra hlt
    push Not at hlt
    apply hj
    refine Finset.mem_image.mpr ⟨(j + m).toNat, Finset.mem_range.mpr (by omega), ?_⟩
    rw [Int.toNat_of_nonneg h]; ring
  · rfl

theorem hasSum_laurentCoeff (P : Polynomial ℂ) (m : ℤ) {Y : ℂ} (hY : Y ≠ 0) :
    HasSum (fun j : ℤ => laurentCoeff P m j * Y ^ j) (Y ^ (-m) * P.eval Y) := by
  classical
  set T : Finset ℤ := (Finset.range (P.natDegree + 1)).image (fun i : ℕ => (i : ℤ) - m) with hT
  have hfin : ∀ j ∉ T, laurentCoeff P m j * Y ^ j = 0 := fun j hj => by
    rw [laurentCoeff_eq_zero_of_not_mem P m hj, zero_mul]
  have hsum : ∑ j ∈ T, laurentCoeff P m j * Y ^ j = Y ^ (-m) * P.eval Y := by
    have hinj : Set.InjOn (fun i : ℕ => (i : ℤ) - m) (Finset.range (P.natDegree + 1) : Set ℕ) := by
      intro i _ i' _ h
      have : (i : ℤ) = i' := by
        have := h
        simp only at this
        linarith
      exact_mod_cast this
    rw [hT, Finset.sum_image hinj, Polynomial.eval_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h0 : 0 ≤ ((i : ℤ) - m) + m := by omega
    simp only [laurentCoeff, if_pos h0]
    rw [show (((i : ℤ) - m) + m).toNat = i by omega, zpow_sub₀ hY, zpow_natCast, zpow_neg, div_eq_mul_inv]
    ring
  rw [← hsum]
  exact hasSum_sum_of_ne_finset_zero hfin

theorem summable_norm_laurentCoeff (P : Polynomial ℂ) (m : ℤ) (r : ℝ) :
    Summable fun j : ℤ => ‖laurentCoeff P m j‖ * r ^ j := by
  classical
  refine summable_of_ne_finset_zero (s := (Finset.range (P.natDegree + 1)).image (fun i : ℕ => (i : ℤ) - m)) ?_
  intro j hj
  rw [laurentCoeff_eq_zero_of_not_mem P m hj, norm_zero, zero_mul]

end Tools

end KcR5P
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_integral_principalSeries2_mul_whittaker_iotaGL_diagUnits2_longWeyl3_eq_mul_of_forall_integral_localZeta31_eq_of_torusShell.KcR5P"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_integral_principalSeries2_mul_whittaker_iotaGL_diagUnits2_longWeyl3_eq_mul_of_forall_integral_localZeta31_eq_of_torusShell.KcR5P"

open KcR5P

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

set_option maxHeartbeats 16000000 in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))

    (V : LocalGL3 p → ℂ) (hVlaw : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ V)
    (hVsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, V (g * k) = V g)
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hVω : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : LocalGL3 p),
      V (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * V g)
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (C₁ : ℂ) (k₁ : ℤ)

    (hT : letI := localBorel ℚ p
      ∀ h : GL (Fin 2) (p.adicCompletion ℚ), ∃ T : Finset ℤ, ∀ n : ℤ, n ∉ T →
        ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
          V (iotaGL (diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
            ^ n * u) * h)) * ((χ 1 u : ℂˣ) : ℂ) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) = 0)

    (h31 : ∀ V' ∈ gl3CyclicSubspace V, ∀ g : LocalGL3 p,
      letI := localBorel ℚ p
      ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
        IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) V' (χ 1) g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) V' (χ 1) s g *
            Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
          Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
        IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          (selfDualHaarAt ℚ p) (dualWhittakerFn3 V') ((χ 1))⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
        (∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
            V' (χ 1) (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
          Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
            (C₁ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k₁ : ℂ) * s))))

    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (P : Polynomial ℂ) (m : ℤ) (σa σb : ℝ) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],

      (∃ σP : ℝ, ∀ s : ℂ, σP < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (V (iotaGL g) * f (w₀p * g)) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
              (s - 1 / 2)) μ₂) →

      (∃ σI : ℝ, ∀ s : ℂ, σI < s.re →
        ∫ y, f (w₀p * unipotentGL2 y) *
          (∫ a, ((χ 0 a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) *
            localZeta31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
              V (χ 1) s (iotaGL (diagUnits2 1 a * unipotentGL2 y))
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∂(selfDualHaarAt ℚ p) =
        (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

      (∀ s : ℂ, σa < s.re → s.re < σb →
        Integrable (fun yat : p.adicCompletion ℚ × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ) =>
          f (w₀p * upperUnipotent2 p yat.1) *
            (((((χ 1) yat.2.1 : ℂˣ) : ℂ)⁻¹ * ((ω yat.2.1 : ℂˣ) : ℂ)⁻¹ *
                ((modulus (yat.2.1 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s *
              ((((χ 0) yat.2.2 : ℂˣ) : ℂ) * ((modulus (yat.2.2 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s - 1))) *
            V (iotaGL (diagUnits2 (yat.2.2 * yat.2.1) yat.2.1) *
              (longWeyl3 * upperUnipotent3 0 0 yat.1 * weylPrime3))))
          ((selfDualHaarAt ℚ p).prod
            ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod
              (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))))) →
      ∀ s : ℂ, σa < s.re → s.re < σb →
        (∫ yat : p.adicCompletion ℚ × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ),
          f (w₀p * upperUnipotent2 p yat.1) *
            (((((χ 1) yat.2.1 : ℂˣ) : ℂ)⁻¹ * ((ω yat.2.1 : ℂˣ) : ℂ)⁻¹ *
                ((modulus (yat.2.1 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s *
              ((((χ 0) yat.2.2 : ℂˣ) : ℂ) * ((modulus (yat.2.2 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s - 1))) *
            V (iotaGL (diagUnits2 (yat.2.2 * yat.2.1) yat.2.1) *
              (longWeyl3 * upperUnipotent3 0 0 yat.1 * weylPrime3)))
          ∂((selfDualHaarAt ℚ p).prod
            ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod
              (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))))) =
        (C₁ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k₁ : ℂ) * (-s))) *
          ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) := by
  intro μ₂ _ hcP hL hcM s hsa hsb
  classical

  haveI : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (p.adicCompletion ℚ)ˣ).IsHaarMeasure :=
    isHaarMeasure_mulHaar p
  haveI : (selfDualHaarAt ℚ p).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt p
  set τ : Measure (p.adicCompletion ℚ)ˣ := Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) with hτdef
  set ν : Measure (p.adicCompletion ℚ) := selfDualHaarAt ℚ p with hνdef
  set qC : ℂ := (Ideal.absNorm p.asIdeal : ℂ) with hqCdef
  set qR : ℝ := (Ideal.absNorm p.asIdeal : ℝ) with hqRdef
  have hqC0 : qC ≠ 0 := qC_ne_zero p
  have hqR1 : 1 < qR := one_lt_qR p
  have hqR0 : 0 < qR := qR_pos p
  obtain ⟨σP, hσP⟩ := hcP
  obtain ⟨σI, hσI⟩ := hL

  set ψ := NumberField.StandardAddChar.psiLocal ℚ p with hψdef
  have hlevel : addCharLevel ψ = 0 := LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p
  have hψk : ∃ k : ℤ, ∀ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp k → ψ x = 1 := by
    refine ⟨0, fun x hx => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p x ?_⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← WithZero.exp_zero]
    exact hx
  obtain ⟨hψn, hψn'⟩ := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ p ψ hψk
    (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)
  rw [hlevel] at hψn hψn'
  have hνnorm : ((ν.real {x : p.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) ^ 2 = 1 := by
    have h := LanglandsTunnell.TateLocal.selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel ℚ p
    rw [hlevel, WithZero.exp_zero] at h
    have hset : ((p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))) = {x : p.adicCompletion ℚ | Valued.v x ≤ 1} := by
      ext x
      exact HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p
    rw [hset] at h
    have h' : (ν.real {x : p.adicCompletion ℚ | Valued.v x ≤ 1}) ^ 2 = 1 := by rw [sq]; exact h
    exact_mod_cast h'

  set cst : p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ → ℂ := fun x =>
    f (w₀p * unipotentGL2 x.1) * (((χ 0 x.2 : ℂˣ) : ℂ) * (((modulus (x.2 : p.adicCompletion ℚ) : ℝ) : ℂ))⁻¹) with hcst

  set hpt : p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ → GL (Fin 2) (p.adicCompletion ℚ) := fun x =>
    diagUnits2 1 x.2 * unipotentGL2 x.1 with hhpt
  set G₁ : (p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ) × ((p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ) → ℂ := fun pq =>
    cst pq.1 * (V (iotaGL (diagUnitGL2 pq.2.1) * lowerUnipotent21 pq.2.2 * iotaGL (hpt pq.1)) *
      (((χ 1 pq.2.1 : ℂˣ) : ℂ) * (((modulus (pq.2.1 : p.adicCompletion ℚ) : ℝ) : ℂ))⁻¹)) with hG₁
  set E₁ : (p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ) × ((p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ) → ℤ := fun pq =>
    ordU p pq.1.2 + ordU p pq.2.1 with hE₁
  set G₂ : (p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ) × (p.adicCompletion ℚ)ˣ → ℂ := fun pa =>
    cst pa.1 * ((((χ 1 pa.2 : ℂˣ) : ℂ))⁻¹ * (((ω pa.2 : ℂˣ) : ℂ))⁻¹ *
      V (iotaGL (diagUnits2 (pa.1.2 * pa.2) pa.2) * (longWeyl3 * upperUnipotent3 0 0 pa.1.1 * weylPrime3))) with hG₂
  set E₂ : (p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ) × (p.adicCompletion ℚ)ˣ → ℤ := fun pa =>
    ordU p pa.1.2 - ordU p pa.2 with hE₂

  set Mid : ℂ → p.adicCompletion ℚ × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ) → ℂ := fun s' yat =>
    f (w₀p * upperUnipotent2 p yat.1) *
      (((((χ 1) yat.2.1 : ℂˣ) : ℂ)⁻¹ * ((ω yat.2.1 : ℂˣ) : ℂ)⁻¹ *
          ((modulus (yat.2.1 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s' *
        ((((χ 0) yat.2.2 : ℂˣ) : ℂ) * ((modulus (yat.2.2 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s' - 1))) *
      V (iotaGL (diagUnits2 (yat.2.2 * yat.2.1) yat.2.1) *
        (longWeyl3 * upperUnipotent3 0 0 yat.1 * weylPrime3))) with hMid

  set HB : ℂ → p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ → ℂ := fun S q =>
    f (w₀p * unipotentGL2 q.1) *
      (((χ 0 q.2.1 : ℂˣ) : ℂ) * ((modulus (q.2.1 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (S - 1)) *
      (V (iotaGL (diagUnitGL2 q.2.2.1) * lowerUnipotent21 q.2.2.2 *
            iotaGL (diagUnits2 1 q.2.1 * unipotentGL2 q.1)) *
        ((χ 1 q.2.2.1 : ℂˣ) : ℂ) * ((modulus (q.2.2.1 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (S - 1)) with hHB

  have hE₁m : Measurable E₁ :=
    ((measurable_ordU (p := p)).comp (measurable_snd.comp measurable_fst)).add
      ((measurable_ordU (p := p)).comp (measurable_fst.comp measurable_snd))
  have hE₂m : Measurable E₂ :=
    ((measurable_ordU (p := p)).comp (measurable_snd.comp measurable_fst)).sub
      ((measurable_ordU (p := p)).comp measurable_snd)

  let eA : ((p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ) × ((p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ)) ≃ᵐ
      (p.adicCompletion ℚ × ((p.adicCompletion ℚ)ˣ × ((p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ))) :=
    MeasurableEquiv.prodAssoc
  have heA : MeasurePreserving eA ((ν.prod τ).prod (τ.prod ν)) (ν.prod (τ.prod (τ.prod ν))) :=
    measurePreserving_prodAssoc ν τ (τ.prod ν)

  let eB : ((p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ) × (p.adicCompletion ℚ)ˣ) ≃ᵐ
      (p.adicCompletion ℚ × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ)) :=
    MeasurableEquiv.prodAssoc.trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) MeasurableEquiv.prodComm)
  have heB : MeasurePreserving eB ((ν.prod τ).prod τ) (ν.prod (τ.prod τ)) := by
    have h1 : MeasurePreserving (MeasurableEquiv.prodAssoc :
        ((p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ) × (p.adicCompletion ℚ)ˣ) ≃ᵐ _)
        ((ν.prod τ).prod τ) (ν.prod (τ.prod τ)) := measurePreserving_prodAssoc ν τ τ
    have h2 : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (p.adicCompletion ℚ))
        (MeasurableEquiv.prodComm : ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ) ≃ᵐ _))
        (ν.prod (τ.prod τ)) (ν.prod (τ.prod τ)) :=
      (MeasurePreserving.id ν).prod (Measure.measurePreserving_swap (μ := τ) (ν := τ))
    exact h2.comp h1
  have heB_apply : ∀ pa : (p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ) × (p.adicCompletion ℚ)ˣ,
      eB pa = (pa.1.1, (pa.2, pa.1.2)) := fun pa => rfl
  have heA_apply : ∀ pq : (p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ) × ((p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ),
      eA pq = (pq.1.1, (pq.1.2, (pq.2.1, pq.2.2))) := fun pq => rfl

  have hYS : ∀ S : ℂ, qC ^ (-S) ≠ 0 := fun S h => hqC0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hYS' : ∀ S : ℂ, qC ^ S ≠ 0 := fun S h => hqC0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hG₁pt : ∀ (S : ℂ) (pq : (p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ) × ((p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ)),
      G₁ pq * (qC ^ (-S)) ^ E₁ pq = HB S (eA pq) := by
    intro S pq
    obtain ⟨⟨y, t⟩, ⟨a, x⟩⟩ := pq
    rw [heA_apply]
    simp only [hG₁, hHB, hcst, hhpt, hE₁]
    rw [zpow_add₀ (hYS S),
      modulus_cpow_sub_one t S, modulus_cpow_sub_one a S]
    ring

  have hG₂pt : ∀ (S : ℂ) (pa : (p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ) × (p.adicCompletion ℚ)ˣ),
      G₂ pa * (qC ^ (-S)) ^ E₂ pa = Mid (-S) (eB pa) := by
    intro S pa
    obtain ⟨⟨y, t⟩, a⟩ := pa
    rw [heB_apply]
    simp only [hG₂, hMid, hcst, hE₂]
    have hcS : qC ^ S = (qC ^ (-S))⁻¹ := by rw [Complex.cpow_neg, inv_inv]
    rw [neg_neg, upperUnipotent2_eq, zpow_sub₀ (hYS S), modulus_cpow_sub_one t S, modulus_cpow a (-S), neg_neg, hcS,
      inv_zpow, div_eq_mul_inv]
    ring

  have hqm : ∀ (n : ℤ) (S : ℂ), qC ^ ((n : ℂ) * S) = (qC ^ (-S)) ^ (-n) := by
    intro n S
    rw [← Complex.cpow_int_mul]
    congr 1
    push_cast
    ring
  have hqm' : ∀ (n : ℤ) (S : ℂ), qC ^ ((n : ℂ) * (-S)) = (qC ^ S) ^ (-n) := by
    intro n S
    rw [← Complex.cpow_int_mul]
    congr 1
    push_cast
    ring
  have hnormr : ∀ r : ℝ, 0 < r → ‖(r : ℂ)‖ = r := fun r hr => by
    rw [Complex.norm_real, Real.norm_of_nonneg hr.le]

  set σst : ℝ := max σP σI with hσst
  set b₁ : ℝ := qR ^ (-σst) with hb₁
  set a₂ : ℝ := qR ^ σa with ha₂
  set b₂ : ℝ := qR ^ σb with hb₂
  have hb₁0 : 0 < b₁ := Real.rpow_pos_of_pos hqR0 _
  have ha₂0 : 0 ≤ a₂ := (Real.rpow_pos_of_pos hqR0 _).le

  have hHB : ∀ S : ℂ, σst < S.re → Integrable (HB S) (ν.prod (τ.prod (τ.prod ν))) := by
    intro S hS
    exact LanglandsTunnell.RankinSelberg.integrable_principalSeries2_mul_whittaker_iotaGL_diagUnitGL2_mul_lowerUnipotent21_of_integrable_whittaker_iotaGL_mul_principalSeries2
      p V χ f hf w₀p hw₀p S μ₂ τ ν (hσP S (lt_of_le_of_lt (le_max_left _ _) hS))
  have hG₁ : ∀ r : ℝ, 0 < r → r < b₁ →
      Integrable (fun pq => G₁ pq * (r : ℂ) ^ E₁ pq) ((ν.prod τ).prod (τ.prod ν)) := by
    intro r hr0 hrb
    obtain ⟨S, hSY, hSre⟩ := exists_cpow_neg_eq p (Y := (r : ℂ)) (by exact_mod_cast hr0.ne')
    have hSgt : σst < S.re := by
      rw [← norm_lt_rpow_neg_iff p S σst, hSre, hnormr r hr0]
      exact hrb
    have h2 : Integrable (HB S ∘ eA) ((ν.prod τ).prod (τ.prod ν)) := heA.integrable_comp_of_integrable (hHB S hSgt)
    refine h2.congr (Filter.Eventually.of_forall fun pq => ?_)
    show HB S (eA pq) = G₁ pq * (r : ℂ) ^ E₁ pq
    rw [← hSY, hG₁pt S pq]

  have hG₂ : ∀ r : ℝ, a₂ < r → r < b₂ →
      Integrable (fun pa => G₂ pa * (r : ℂ) ^ E₂ pa) ((ν.prod τ).prod τ) := by
    intro r hra hrb
    have hr0 : 0 < r := lt_of_le_of_lt ha₂0 hra
    obtain ⟨S, hSY, hSre⟩ := exists_cpow_neg_eq p (Y := (r : ℂ)) (by exact_mod_cast hr0.ne')
    rw [hnormr r hr0] at hSre
    have h1 : σa < (-S).re := by
      rw [Complex.neg_re]
      have h := (rpow_lt_norm_iff p S σa).mp (by rw [hSre]; exact hra)
      linarith
    have h2 : (-S).re < σb := by
      rw [Complex.neg_re]
      have h : qR ^ (-S.re) < qR ^ σb := by rw [hSre]; exact hrb
      exact (Real.rpow_lt_rpow_left_iff hqR1).mp h
    have hint : Integrable (Mid (-S)) (ν.prod (τ.prod τ)) := hcM (-S) h1 h2
    have h3 : Integrable (Mid (-S) ∘ eB) ((ν.prod τ).prod τ) := heB.integrable_comp_of_integrable hint
    refine h3.congr (Filter.Eventually.of_forall fun pa => ?_)
    show Mid (-S) (eB pa) = G₂ pa * (r : ℂ) ^ E₂ pa
    rw [← hSY, hG₂pt S pa]

  have hA₁ : ∀ Y : ℂ, 0 < ‖Y‖ → ‖Y‖ < b₁ →
      ∫ pq, G₁ pq * Y ^ E₁ pq ∂((ν.prod τ).prod (τ.prod ν)) = Y ^ (-m) * P.eval Y := by
    intro Y hY0 hYb
    have hYne : Y ≠ 0 := norm_pos_iff.mp hY0
    obtain ⟨S, hSY, hSre⟩ := exists_cpow_neg_eq p hYne
    have hSgt : σst < S.re := by
      rw [← norm_lt_rpow_neg_iff p S σst, hSre]
      exact hYb
    have hint := hHB S hSgt
    set g : (p.adicCompletion ℚ)ˣ → p.adicCompletion ℚ → LocalGL3 p := fun t y =>
      iotaGL (diagUnits2 1 t * unipotentGL2 y) with hg
    calc ∫ pq, G₁ pq * Y ^ E₁ pq ∂((ν.prod τ).prod (τ.prod ν))
        = ∫ pq, HB S (eA pq) ∂((ν.prod τ).prod (τ.prod ν)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun pq => ?_)
          show G₁ pq * Y ^ E₁ pq = HB S (eA pq)
          rw [← hSY, hG₁pt S pq]
      _ = ∫ q, HB S q ∂(ν.prod (τ.prod (τ.prod ν))) := heA.integral_comp' (HB S)
      _ = ∫ y, ∫ t, ∫ a, ∫ x, HB S (y, t, a, x) ∂ν ∂τ ∂τ ∂ν := integral_prod_four ν τ τ ν (HB S) hint
      _ = ∫ y, f (w₀p * unipotentGL2 y) *
            (∫ t, ((χ 0 t : ℂˣ) : ℂ) * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (S - 1) *
              localZeta31 p τ ν V (χ 1) S (iotaGL (diagUnits2 1 t * unipotentGL2 y)) ∂τ) ∂ν := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          beta_reduce
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          beta_reduce
          unfold localZeta31
          rw [← integral_const_mul, ← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
          beta_reduce
          rw [show (fun x : p.adicCompletion ℚ => HB S (y, t, a, x)) = fun x =>
              (f (w₀p * unipotentGL2 y) *
                (((χ 0 t : ℂˣ) : ℂ) * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (S - 1))) *
              (V (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * iotaGL (diagUnits2 1 t * unipotentGL2 y)) *
                ((χ 1 a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (S - 1)) from rfl]
          rw [integral_const_mul, integral_mul_const, integral_mul_const]
          ring
      _ = qC ^ ((m : ℂ) * S) * P.eval (qC ^ (-S)) := hσI S (lt_of_le_of_lt (le_max_right _ _) hSgt)
      _ = Y ^ (-m) * P.eval Y := by rw [hqm m S, hSY]

  have hfe : ∀ᵐ x ∂(ν.prod τ), ∃ (Px : Polynomial ℂ) (nx : ℤ) (a₁' b₁' a₂' b₂' : ℝ),
      0 ≤ a₁' ∧ a₁' < b₁' ∧ 0 ≤ a₂' ∧ a₂' < b₂' ∧
      (∀ Y : ℂ, a₁' < ‖Y‖ → ‖Y‖ < b₁' →
        Integrable (fun tt => G₁ (x, tt) * Y ^ E₁ (x, tt)) (τ.prod ν) ∧
        (∫ tt, G₁ (x, tt) * Y ^ E₁ (x, tt) ∂(τ.prod ν)) * (1 : Polynomial ℂ).eval Y = Px.eval Y * Y ^ nx) ∧
      (∀ Y : ℂ, a₂' < ‖Y‖ → ‖Y‖ < b₂' →
        Integrable (fun tt => G₂ (x, tt) * Y ^ E₂ (x, tt)) τ ∧
        (∫ tt, G₂ (x, tt) * Y ^ E₂ (x, tt) ∂τ) * (1 : Polynomial ℂ).eval Y = C₁ * Y ^ (-k₁) * (Px.eval Y * Y ^ nx)) := by
    refine ae_of_all _ fun x => ?_
    obtain ⟨y, t⟩ := x

    obtain ⟨Ph, mh, σ₀h, σ₁h, Rh, hc31, hZ1, hc30, hZ0⟩ :=
      LanglandsTunnell.RankinSelberg.exists_polynomial_localZeta31_iotaGL_eq_and_localZeta30_dualWhittakerFn3_eq_mul_of_forall_mem_gl3CyclicSubspace_fe_of_torusShell
        p hπ hϖ ψ 0 hψn hψn' V hVlaw hVsm (χ 1) C₁ k₁ (hpt (y, t)) τ ν hT
        (fun V' hV' => h31 V' hV' (iotaGL (hpt (y, t))))

    have hZ0' : ∀ S : ℂ, σ₁h < (1 - S).re → qR ^ (-S.re) ∉ Rh →
        localZeta30 p τ (dualWhittakerFn3 V) (χ 1)⁻¹ (1 - S) (weylPrime3 * transposeInv3 (iotaGL (hpt (y, t)))) =
          C₁ * qC ^ ((k₁ : ℂ) * S) * (qC ^ ((mh : ℂ) * S) * Ph.eval (qC ^ (-S))) := by
      intro S hS hR
      have h := hZ0 S hS hR
      rw [zpow_zero, hνnorm, one_mul, one_mul] at h
      exact h
    set cx : ℂ := cst (y, t) with hcx
    refine ⟨Polynomial.C cx * Ph, ordU p t - mh, 0, qR ^ (-σ₀h), 1 + qR ^ (σ₁h - 1) + ∑ r ∈ Rh, |r|,
      1 + qR ^ (σ₁h - 1) + ∑ r ∈ Rh, |r| + 1, le_rfl, Real.rpow_pos_of_pos hqR0 _, ?_, by linarith, ?_, ?_⟩
    · have h1 : 0 < qR ^ (σ₁h - 1) := Real.rpow_pos_of_pos hqR0 _
      have h2 : 0 ≤ ∑ r ∈ Rh, |r| := Finset.sum_nonneg fun r _ => abs_nonneg r
      linarith
    ·
      intro Y hY0 hYb
      have hYne : Y ≠ 0 := norm_pos_iff.mp hY0
      obtain ⟨S, hSY, hSre⟩ := exists_cpow_neg_eq p hYne
      have hSgt : σ₀h < S.re := by
        rw [← norm_lt_rpow_neg_iff p S σ₀h, hSre]
        exact hYb
      have hI31 := hc31 S hSgt
      have hpt1 : ∀ tt : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ,
          G₁ ((y, t), tt) * Y ^ E₁ ((y, t), tt) =
            (cx * Y ^ ordU p t) *
              (V (iotaGL (diagUnitGL2 tt.1) * lowerUnipotent21 tt.2 * iotaGL (hpt (y, t))) * ((χ 1 tt.1 : ℂˣ) : ℂ) *
                ((modulus (tt.1 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (S - 1)) := by
        intro tt
        obtain ⟨a, xx⟩ := tt
        rw [← hSY]
        simp only [hE₁, hcx]
        rw [zpow_add₀ (hYS S), modulus_cpow_sub_one a S]
        ring
      refine ⟨(hI31.const_mul (cx * Y ^ ordU p t)).congr (Filter.Eventually.of_forall fun tt => (hpt1 tt).symm), ?_⟩
      have hint1 : ∫ tt, G₁ ((y, t), tt) * Y ^ E₁ ((y, t), tt) ∂(τ.prod ν) =
          (cx * Y ^ ordU p t) * localZeta31 p τ ν V (χ 1) S (iotaGL (hpt (y, t))) := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hpt1), integral_const_mul, integral_prod _ hI31]
        unfold localZeta31
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        show ∫ xx, V (iotaGL (diagUnitGL2 (a, xx).1) * lowerUnipotent21 (a, xx).2 * iotaGL (hpt (y, t))) *
            ((χ 1 (a, xx).1 : ℂˣ) : ℂ) * ((modulus ((a, xx).1 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (S - 1) ∂ν = _
        simp only []
        rw [integral_mul_const, integral_mul_const]
      rw [hint1, hZ1 S hSgt, Polynomial.eval_one, mul_one, Polynomial.eval_mul, Polynomial.eval_C, hqm mh S, hSY,
        zpow_sub₀ hYne, zpow_neg, div_eq_mul_inv]
      ring
    ·
      intro Y hYa hYb
      have hpos1 : 0 < qR ^ (σ₁h - 1) := Real.rpow_pos_of_pos hqR0 _
      have hsum0 : 0 ≤ ∑ r ∈ Rh, |r| := Finset.sum_nonneg fun r _ => abs_nonneg r
      have hY0 : 0 < ‖Y‖ := by linarith
      have hYne : Y ≠ 0 := norm_pos_iff.mp hY0
      obtain ⟨S, hSY, hSre⟩ := exists_cpow_neg_eq p hYne
      have hS1 : σ₁h < (1 - S).re := by
        rw [Complex.sub_re, Complex.one_re]
        have h : qR ^ (σ₁h - 1) < qR ^ (-S.re) := by rw [hSre]; linarith
        have := (Real.rpow_lt_rpow_left_iff hqR1).mp h
        linarith
      have hSR : qR ^ (-S.re) ∉ Rh := by
        intro hmem
        have hle : |qR ^ (-S.re)| ≤ ∑ r ∈ Rh, |r| := Finset.single_le_sum (fun r _ => abs_nonneg r) hmem
        rw [hSre, abs_of_pos hY0] at hle
        linarith
      have hI30 := hc30 (1 - S) hS1
      have hpt2 : ∀ a : (p.adicCompletion ℚ)ˣ,
          G₂ ((y, t), a) * Y ^ E₂ ((y, t), a) =
            (cx * Y ^ ordU p t) *
              (dualWhittakerFn3 V (iotaGL (diagUnitGL2 a) * (weylPrime3 * transposeInv3 (iotaGL (hpt (y, t))))) *
                (((χ 1)⁻¹ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - S - 1)) := by
        intro a
        rw [← hSY]
        simp only [hE₂, hcx, hhpt]
        have hcS : qC ^ S = (qC ^ (-S))⁻¹ := by rw [Complex.cpow_neg, inv_inv]
        rw [dual_point V ω hVω a t y, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
          show (1 : ℂ) - S - 1 = -S by ring, modulus_cpow a (-S), neg_neg, hcS, inv_zpow, zpow_sub₀ (hYS S),
          div_eq_mul_inv]
        ring
      refine ⟨(hI30.const_mul (cx * Y ^ ordU p t)).congr (Filter.Eventually.of_forall fun a => (hpt2 a).symm), ?_⟩
      have hint2 : ∫ a, G₂ ((y, t), a) * Y ^ E₂ ((y, t), a) ∂τ =
          (cx * Y ^ ordU p t) *
            localZeta30 p τ (dualWhittakerFn3 V) (χ 1)⁻¹ (1 - S) (weylPrime3 * transposeInv3 (iotaGL (hpt (y, t)))) := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hpt2), integral_const_mul]
        rfl
      rw [hint2, hZ0' S hS1 hSR, Polynomial.eval_one, mul_one, Polynomial.eval_mul, Polynomial.eval_C, hqm mh S,
        hqm k₁ S, hSY, zpow_sub₀ hYne, zpow_neg, zpow_neg, div_eq_mul_inv]
      ring

  obtain ⟨e, hes₁, he₁, hes₂, he₂⟩ :=
    MeasureTheory.exists_hasSum_mul_zpow_eval_mul_integral_prod_of_ae_forall_integral_mul_zpow_mul_eval_eq
      (ν.prod τ) (τ.prod ν) τ E₁ hE₁m E₂ hE₂m G₁ G₂ (a₁ := 0) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) le_rfl ha₂0
      hG₁ hG₂ 1 1 C₁ (-k₁) hfe

  have hec : e = laurentCoeff P m := by
    set r₁ : ℝ := b₁ / 3 with hr₁
    set r₂ : ℝ := 2 * b₁ / 3 with hr₂
    have hr₁0 : 0 < r₁ := by rw [hr₁]; linarith
    have hr₁₂ : r₁ < r₂ := by rw [hr₁, hr₂]; linarith
    have hr₂b : r₂ < b₁ := by rw [hr₂]; linarith
    have hsum : ∀ r : ℝ, 0 < r → r < b₁ → Summable fun j : ℤ => ‖e j - laurentCoeff P m j‖ * r ^ j := by
      intro r hr0 hrb
      refine Summable.of_nonneg_of_le (fun j => mul_nonneg (norm_nonneg _) (zpow_pos hr0 j).le) (fun j => ?_)
        ((hes₁ r hr0 hrb).add (summable_norm_laurentCoeff P m r))
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (zpow_pos hr0 j).le
    have hz : ∀ z : ℂ, r₁ < ‖z‖ → ‖z‖ < r₂ → ∑' j : ℤ, (e j - laurentCoeff P m j) * z ^ j = 0 := by
      intro z hz1 hz2
      have hz0 : 0 < ‖z‖ := lt_trans hr₁0 hz1
      have hzb : ‖z‖ < b₁ := lt_trans hz2 hr₂b
      have hzne : z ≠ 0 := norm_pos_iff.mp hz0
      have h1 := he₁ z hz0 hzb
      rw [Polynomial.eval_one, one_mul, hA₁ z hz0 hzb] at h1
      have h2 := hasSum_laurentCoeff P m hzne
      have h3 := h1.sub h2
      rw [sub_self] at h3
      rw [← h3.tsum_eq]
      refine tsum_congr fun j => ?_
      ring
    have hd := Complex.eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero
      (fun j => e j - laurentCoeff P m j) hr₁0 hr₁₂ (hsum r₁ hr₁0 (lt_trans hr₁₂ hr₂b)) (hsum r₂ (lt_trans hr₁0 hr₁₂) hr₂b) hz
    funext j
    have := congr_fun hd j
    exact sub_eq_zero.mp this

  set Y : ℂ := qC ^ s with hYdef
  have hYne : Y ≠ 0 := hYS' s
  have hYnorm : ‖Y‖ = qR ^ s.re := norm_qC_cpow p s
  have hYa : a₂ < ‖Y‖ := by rw [hYnorm]; exact (Real.rpow_lt_rpow_left_iff hqR1).mpr hsa
  have hYb : ‖Y‖ < b₂ := by rw [hYnorm]; exact (Real.rpow_lt_rpow_left_iff hqR1).mpr hsb
  have hmid := he₂ Y hYa hYb
  rw [Polynomial.eval_one, one_mul, hec] at hmid

  have hlc : HasSum (fun j : ℤ => C₁ * laurentCoeff P m (j - -k₁) * Y ^ j) (C₁ * Y ^ (-k₁) * (Y ^ (-m) * P.eval Y)) := by
    have h1 := hasSum_laurentCoeff P m hYne
    have h2 : HasSum (fun j : ℤ => laurentCoeff P m (j + k₁) * Y ^ (j + k₁)) (Y ^ (-m) * P.eval Y) :=
      (Equiv.addRight k₁).hasSum_iff.mpr h1
    have h3 := h2.mul_left (C₁ * Y ^ (-k₁))
    refine h3.congr_fun fun j => ?_
    rw [sub_neg_eq_add, zpow_add₀ hYne, zpow_neg]
    field_simp
  have hval : ∫ pa, G₂ pa * Y ^ E₂ pa ∂((ν.prod τ).prod τ) = C₁ * Y ^ (-k₁) * (Y ^ (-m) * P.eval Y) :=
    hmid.unique hlc

  have hint : ∫ pa, G₂ pa * Y ^ E₂ pa ∂((ν.prod τ).prod τ) = ∫ yat, Mid s yat ∂(ν.prod (τ.prod τ)) := by
    rw [← heB.integral_comp' (Mid s)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun pa => ?_)
    show G₂ pa * Y ^ E₂ pa = Mid s (eB pa)
    have h := hG₂pt (-s) pa
    rw [neg_neg] at h
    rw [← h]
  change ∫ yat, Mid s yat ∂(ν.prod (τ.prod τ)) = _
  rw [← hint, hval, hqm' k₁ s, hqm' m s]

end S_LanglandsTunnell_RankinSelberg_integral_principalSeries2_mul_whittaker_iotaGL_diagUnits2_longWeyl3_eq_mul_of_forall_integral_localZeta31_eq_of_torusShell
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_integral_principalSeries2_mul_whittaker_iotaGL_diagUnits2_longWeyl3_eq_mul_of_forall_integral_localZeta31_eq_of_torusShell (solution)
