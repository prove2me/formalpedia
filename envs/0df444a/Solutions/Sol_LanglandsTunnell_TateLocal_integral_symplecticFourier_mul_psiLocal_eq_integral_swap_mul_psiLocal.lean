-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.integral_symplecticFourier_mul_psiLocal_eq_integral_swap_mul_psiLocal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/0d3443aa-c593-5849-a7f5-08b727a9fecf

import Mathlib
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_tateFourier_psiLocal_selfDualHaarAt_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_finset_forall_eq_sum_mul_prod_indicator_ball_of_isLocallyConstant_of_hasCompactSupport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_integral_symplecticFourier_mul_psiLocal_eq_integral_swap_mul_psiLocal
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal Filter Topology
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace SwapD2R

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "ψ" => (NumberField.StandardAddChar.psiLocal ℚ p)
local notation "ν" => (selfDualHaarAt ℚ p)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem isAddHaarMeasure_sd : (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  have : selfDualHaarAt ℚ p = Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := by
    unfold selfDualHaarAt
    rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p]
    simp
  rw [this]; infer_instance

attribute [local instance] isAddHaarMeasure_sd

def ballc (N : ℤ) (c : F) : Set F := {x | Valued.v (x - c) ≤ WithZero.exp N}

def ind (N : ℤ) (c : F) : F → ℂ := (ballc p N c).indicator fun _ => (1 : ℂ)

theorem ballc_eq_preimage (N : ℤ) (c : F) :
    ballc p N c = (fun x : F => x - c) ⁻¹' {y : F | Valued.v y ≤ WithZero.exp N} := rfl

theorem ballc_eq_image (N : ℤ) (c : F) :
    ballc p N c = (fun y : F => y + c) '' {y : F | Valued.v y ≤ WithZero.exp N} := by
  ext x
  simp only [ballc, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hx
    exact ⟨x - c, hx, by ring⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem exists_valued_eq (N : ℤ) : ∃ t : F, t ≠ 0 ∧ Valued.v t = WithZero.exp N := by
  obtain ⟨t, ht, hvt⟩ := AdelicLevel.exists_valued_eq_exp_neg (K := ℚ) p 1
  refine ⟨t ^ (-N), zpow_ne_zero _ ht, ?_⟩
  rw [map_zpow₀, hvt, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem isClosed_ballc (N : ℤ) (c : F) : IsClosed (ballc p N c) := by
  obtain ⟨t, ht, hvt⟩ := exists_valued_eq p N
  rw [ballc_eq_preimage, ← hvt]
  exact (AdelicLevel.isClosed_setOf_valued_le p t ht).preimage (continuous_id.sub continuous_const)

theorem isOpen_ballc (N : ℤ) (c : F) : IsOpen (ballc p N c) := by
  obtain ⟨t, ht, hvt⟩ := exists_valued_eq p N
  rw [ballc_eq_preimage, ← hvt]
  exact (AdelicLevel.isOpen_setOf_valued_le p t ht).preimage (continuous_id.sub continuous_const)

theorem isCompact_ball0 (N : ℤ) : IsCompact {y : F | Valued.v y ≤ WithZero.exp N} := by
  obtain ⟨t, ht, hvt⟩ := exists_valued_eq p N
  have : {y : F | Valued.v y ≤ WithZero.exp N} = t • ((HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F)) := by
    ext y
    rw [Set.mem_smul_set]
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
    constructor
    · intro hy
      refine ⟨t⁻¹ * y, ?_, by rw [smul_eq_mul, mul_inv_cancel_left₀ ht]⟩
      rw [map_mul, map_inv₀, hvt]
      calc (WithZero.exp N)⁻¹ * Valued.v y ≤ (WithZero.exp N)⁻¹ * WithZero.exp N := mul_le_mul_right hy _
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · rintro ⟨z, hz, rfl⟩
      rw [smul_eq_mul, map_mul, hvt]
      calc WithZero.exp N * Valued.v z ≤ WithZero.exp N * 1 := mul_le_mul_right hz _
        _ = WithZero.exp N := mul_one _
  rw [this, ← coe_integersPositiveCompacts ℚ p]
  exact (integersPositiveCompacts ℚ p).isCompact.smul _

theorem isCompact_ballc (N : ℤ) (c : F) : IsCompact (ballc p N c) := by
  rw [ballc_eq_image]
  exact (isCompact_ball0 p N).image (continuous_id.add continuous_const)

theorem measurableSet_ballc (N : ℤ) (c : F) : MeasurableSet (ballc p N c) := (isClosed_ballc p N c).measurableSet

theorem isSchwartzBruhat_ind (N : ℤ) (c : F) : IsSchwartzBruhat (ind p N c) :=
  IsSchwartzBruhat.indicator_const ⟨isClosed_ballc p N c, isOpen_ballc p N c⟩ (isCompact_ballc p N c) 1

theorem norm_ind_le (N : ℤ) (c x : F) : ‖ind p N c x‖ ≤ 1 := by
  unfold ind
  by_cases hx : x ∈ ballc p N c
  · rw [Set.indicator_of_mem hx, norm_one]
  · rw [Set.indicator_of_notMem hx, norm_zero]; exact zero_le_one

theorem measurable_ind (N : ℤ) (c : F) : Measurable (ind p N c) :=
  (measurable_const.indicator (measurableSet_ballc p N c))

theorem psi_level : (∀ x : F, Valued.v x ≤ WithZero.exp (0 : ℤ) → ψ x = 1) ∧
    ∃ x : F, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ ψ x ≠ 1 := by
  have h0 : ∀ x : F, Valued.v x ≤ WithZero.exp (0 : ℤ) → ψ x = 1 := by
    intro x hx
    apply LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simpa using hx
  have h := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ p ψ ⟨0, h0⟩
    (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)
  rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p] at h
  exact ⟨h0, h.2⟩

theorem norm_psi_le_one (w : F) : ‖ψ w‖ ≤ 1 := by

  have hw0 : ∃ k : ℤ, Valued.v w ≤ WithZero.exp k := by
    by_cases hw : w = 0
    · exact ⟨0, by simp [hw]⟩
    · exact ⟨WithZero.log (Valued.v w), by rw [WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hw)]⟩
  obtain ⟨k, hk⟩ := hw0
  have hcpt : IsCompact {y : F | Valued.v y ≤ WithZero.exp k} := isCompact_ball0 p k
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn
    (NumberField.StandardAddChar.continuous_psiLocal ℚ p).continuousOn
  by_contra hlt
  rw [not_le] at hlt
  have hnat : ∀ j : ℕ, Valued.v ((j : F)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      push_cast
      exact (Valuation.map_add _ _ _).trans (max_le ih (by simp))
  have hpow : ∀ j : ℕ, ‖ψ w‖ ^ j ≤ C := by
    intro j
    have hju : (j : F) * w ∈ {y : F | Valued.v y ≤ WithZero.exp k} := by
      rw [Set.mem_setOf_eq, map_mul]
      calc Valued.v (j : F) * Valued.v w ≤ 1 * Valued.v w := mul_le_mul_left (hnat j) _
        _ ≤ WithZero.exp k := by rw [one_mul]; exact hk
    have := hC _ hju
    rwa [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, norm_pow] at this
  have ht := tendsto_pow_atTop_atTop_of_one_lt hlt
  rw [Filter.tendsto_atTop_atTop] at ht
  obtain ⟨j, hj⟩ := ht (C + 1)
  linarith [hpow j, hj j le_rfl]

theorem tateFourier_ind (N : ℤ) (c y : F) :
    tateFourier ψ ν (ind p N c) y =
      ψ (c * y) * (((selfDualHaarAt ℚ p).real {x : F | Valued.v x ≤ WithZero.exp (-(-N))} : ℝ) : ℂ) *
        {y' : F | Valued.v y' ≤ WithZero.exp ((0 : ℤ) + -N)}.indicator (fun _ => (1 : ℂ)) y := by
  have h := LanglandsTunnell.TateLocal.tateFourier_indicator_setOf_valued_sub_le ℚ p ν ψ 0
    (psi_level p).1 (psi_level p).2 c (-N) y
  simpa only [ind, ballc, neg_neg] using h

theorem integrable_tateFourier_ind_neg_mul (N : ℤ) (c b : F) (C : ℂ) :
    Integrable (fun y : F => C * tateFourier ψ ν (ind p N c) (-y) * ψ (b * y)) ν := by

  set V : ℂ := (((selfDualHaarAt ℚ p).real {x : F | Valued.v x ≤ WithZero.exp (-(-N))} : ℝ) : ℂ) with hV
  set S : Set F := {y' : F | Valued.v y' ≤ WithZero.exp ((0 : ℤ) + -N)} with hS
  have hSm : MeasurableSet S := by
    have : S = ballc p (0 + -N) 0 := by ext y; simp [hS, ballc]
    rw [this]; exact measurableSet_ballc p _ _
  have hSc : IsCompact S := by rw [hS]; exact isCompact_ball0 p _
  have hform : (fun y : F => C * tateFourier ψ ν (ind p N c) (-y) * ψ (b * y)) =
      fun y : F => S.indicator (fun y => C * (ψ (c * -y) * V) * ψ (b * y)) y := by
    funext y
    rw [tateFourier_ind]
    have hneg : (-y ∈ S) ↔ (y ∈ S) := by simp [hS]
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem (hneg.mpr hy), Set.indicator_of_mem hy]; ring
    · rw [Set.indicator_of_notMem (fun h => hy (hneg.mp h)), Set.indicator_of_notMem hy]; ring
  rw [hform, integrable_indicator_iff hSm]
  refine Measure.integrableOn_of_bounded (M := ‖C‖ * ‖V‖) hSc.measure_lt_top.ne ?_ ?_
  · exact ((continuous_const.mul (((NumberField.StandardAddChar.continuous_psiLocal ℚ p).comp
      (continuous_const.mul continuous_neg)).mul continuous_const)).mul
      ((NumberField.StandardAddChar.continuous_psiLocal ℚ p).comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  · refine Eventually.of_forall fun y => ?_
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖C‖ * (‖ψ (c * -y)‖ * ‖V‖) * ‖ψ (b * y)‖ ≤ ‖C‖ * (1 * ‖V‖) * 1 := by
          gcongr
          · exact norm_psi_le_one p _
          · exact norm_psi_le_one p _
      _ = ‖C‖ * ‖V‖ := by ring

theorem swap_box_inner (N : ℤ) (c0 c1 : F) (C : ℂ) (a y : F) :
    (∫ u : Fin 2 → F, (C * (ind p N c0 (u 0) * ind p N c1 (u 1))) * ψ (u 1 * a - u 0 * y)
        ∂(Measure.pi fun _ : Fin 2 => ν)) =
      C * tateFourier ψ ν (ind p N c0) (-y) * ∫ x : F, ind p N c1 x * ψ (x * a) ∂ν := by
  have hmp := MeasureTheory.measurePreserving_finTwoArrow (selfDualHaarAt ℚ p)
  have hcomp := hmp.integral_comp (MeasurableEquiv.finTwoArrow).measurableEmbedding
    (fun z : F × F => (C * (ind p N c0 z.1 * ind p N c1 z.2)) * ψ (z.2 * a - z.1 * y))
  have hlhs : (fun u : Fin 2 → F => (C * (ind p N c0 (u 0) * ind p N c1 (u 1))) * ψ (u 1 * a - u 0 * y)) =
      fun u : Fin 2 → F => (fun z : F × F => (C * (ind p N c0 z.1 * ind p N c1 z.2)) * ψ (z.2 * a - z.1 * y))
        (MeasurableEquiv.finTwoArrow u) := by
    funext u; rfl
  rw [hlhs, hcomp]
  have hsplit : (fun z : F × F => (C * (ind p N c0 z.1 * ind p N c1 z.2)) * ψ (z.2 * a - z.1 * y)) =
      fun z : F × F => (C * (ind p N c0 z.1 * ψ (z.1 * -y))) * (ind p N c1 z.2 * ψ (z.2 * a)) := by
    funext z
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul, show -(z.1 * y) = z.1 * -y by ring]
    ring
  rw [hsplit, MeasureTheory.integral_prod_mul
    (fun x : F => C * (ind p N c0 x * ψ (x * -y))) (fun x : F => ind p N c1 x * ψ (x * a)),
    integral_const_mul]
  rfl

theorem swap_box (N : ℤ) (c0 c1 : F) (C : ℂ) (a b : F) :
    ∫ y : F, (fun v : Fin 2 → F =>
        ∫ u : Fin 2 → F, (C * (ind p N c0 (u 0) * ind p N c1 (u 1))) * ψ (u 1 * v 0 - u 0 * v 1)
          ∂(Measure.pi fun _ : Fin 2 => ν)) ![a, y] * ψ (b * y) ∂ν =
      ∫ y : F, (C * (ind p N c0 (![b, y] 0) * ind p N c1 (![b, y] 1))) * ψ (a * y) ∂ν := by
  set G1 : ℂ := ∫ x : F, ind p N c1 x * ψ (x * a) ∂ν with hG1

  have hlam : ∀ y : F, (fun v : Fin 2 → F =>
        ∫ u : Fin 2 → F, (C * (ind p N c0 (u 0) * ind p N c1 (u 1))) * ψ (u 1 * v 0 - u 0 * v 1)
          ∂(Measure.pi fun _ : Fin 2 => ν)) ![a, y] =
      C * tateFourier ψ ν (ind p N c0) (-y) * G1 := by
    intro y
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [swap_box_inner, hG1]
  simp_rw [hlam]

  have hL : ∫ y : F, C * tateFourier ψ ν (ind p N c0) (-y) * G1 * ψ (b * y) ∂ν =
      G1 * (C * ∫ y : F, tateFourier ψ ν (ind p N c0) (-y) * ψ (b * y) ∂ν) := by
    rw [← integral_const_mul, ← integral_const_mul]
    congr 1; funext y; ring
  have hrefl : ∫ y : F, tateFourier ψ ν (ind p N c0) (-y) * ψ (b * y) ∂ν =
      ∫ y : F, tateFourier ψ ν (ind p N c0) y * ψ (y * -b) ∂ν := by
    have := integral_neg_eq_self (fun y : F => tateFourier ψ ν (ind p N c0) y * ψ (y * -b)) ν

    rw [← this]
    congr 1; funext y
    rw [show -y * -b = b * y by ring]
  have hinv : ∫ y : F, tateFourier ψ ν (ind p N c0) y * ψ (y * -b) ∂ν = ind p N c0 b := by
    have := LanglandsTunnell.TateLocal.tateFourier_tateFourier_psiLocal_selfDualHaarAt_rat p (ind p N c0)
      (isSchwartzBruhat_ind p N c0) (-b)
    rw [neg_neg] at this
    rw [← this]
    rfl
  rw [hL, hrefl, hinv]

  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hR : ∫ y : F, C * (ind p N c0 b * ind p N c1 y) * ψ (a * y) ∂ν =
      C * ind p N c0 b * ∫ y : F, ind p N c1 y * ψ (y * a) ∂ν := by
    rw [← integral_const_mul]
    congr 1; funext y
    rw [mul_comm a y]; ring
  rw [hR, hG1]
  ring

theorem swap_main (Ψ : (Fin 2 → F) → ℂ) (hΨ : IsLocallyConstant Ψ ∧ HasCompactSupport Ψ) (a b : F) :
    ∫ y : F, (fun v : Fin 2 → F =>
        ∫ u : Fin 2 → F, Ψ u * ψ (u 1 * v 0 - u 0 * v 1) ∂(Measure.pi fun _ : Fin 2 => ν)) ![a, y] *
          ψ (b * y) ∂ν =
      ∫ y : F, Ψ ![b, y] * ψ (a * y) ∂ν := by
  obtain ⟨N, S, -, hdec⟩ :=
    LanglandsTunnell.TateLocal.exists_finset_forall_eq_sum_mul_prod_indicator_ball_of_isLocallyConstant_of_hasCompactSupport
      p 2 Ψ hΨ.1 hΨ.2

  have hdec' : ∀ v : Fin 2 → F, Ψ v = ∑ c ∈ S, Ψ c * (ind p N (c 0) (v 0) * ind p N (c 1) (v 1)) := by
    intro v
    rw [hdec v]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Fin.prod_univ_two]
    rfl

  have hint_box : ∀ (c : Fin 2 → F) (v0 v1 : F), Integrable (fun u : Fin 2 → F =>
      Ψ c * (ind p N (c 0) (u 0) * ind p N (c 1) (u 1)) * ψ (u 1 * v0 - u 0 * v1)) (Measure.pi fun _ : Fin 2 => ν) := by
    intro c v0 v1

    set B : Set (Fin 2 → F) := Set.pi Set.univ (fun j : Fin 2 => ballc p N (c j)) with hB
    have hBm : MeasurableSet B := MeasurableSet.univ_pi fun j => measurableSet_ballc p N (c j)
    have hBfin : (Measure.pi fun _ : Fin 2 => ν) B < ⊤ := by
      rw [hB, Measure.pi_pi]
      exact ENNReal.prod_lt_top fun j _ => (isCompact_ballc p N (c j)).measure_lt_top
    have hform : (fun u : Fin 2 → F => Ψ c * (ind p N (c 0) (u 0) * ind p N (c 1) (u 1)) * ψ (u 1 * v0 - u 0 * v1)) =
        fun u => B.indicator (fun u => Ψ c * ψ (u 1 * v0 - u 0 * v1)) u := by
      funext u
      unfold ind
      by_cases h0 : u 0 ∈ ballc p N (c 0)
      · by_cases h1 : u 1 ∈ ballc p N (c 1)
        · have hu : u ∈ B := by
            rw [hB, Set.mem_univ_pi]; intro j; fin_cases j <;> assumption
          rw [Set.indicator_of_mem h0, Set.indicator_of_mem h1, Set.indicator_of_mem hu]; ring
        · have hu : u ∉ B := fun h => h1 ((Set.mem_univ_pi.mp (hB ▸ h)) 1)
          rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem hu]; ring
      · have hu : u ∉ B := fun h => h0 ((Set.mem_univ_pi.mp (hB ▸ h)) 0)
        rw [Set.indicator_of_notMem h0, Set.indicator_of_notMem hu]; ring
    rw [hform, integrable_indicator_iff hBm]
    refine Measure.integrableOn_of_bounded (M := ‖Ψ c‖) hBfin.ne ?_ ?_
    · exact (continuous_const.mul ((NumberField.StandardAddChar.continuous_psiLocal ℚ p).comp
        (((continuous_apply 1).mul continuous_const).sub ((continuous_apply 0).mul continuous_const)))).aestronglyMeasurable
    · refine Eventually.of_forall fun u => ?_
      rw [norm_mul]
      calc ‖Ψ c‖ * ‖ψ (u 1 * v0 - u 0 * v1)‖ ≤ ‖Ψ c‖ * 1 := by gcongr; exact norm_psi_le_one p _
        _ = ‖Ψ c‖ := mul_one _

  have hinner : ∀ v0 v1 : F,
      (∫ u : Fin 2 → F, Ψ u * ψ (u 1 * v0 - u 0 * v1) ∂(Measure.pi fun _ : Fin 2 => ν)) =
        ∑ c ∈ S, ∫ u : Fin 2 → F, Ψ c * (ind p N (c 0) (u 0) * ind p N (c 1) (u 1)) * ψ (u 1 * v0 - u 0 * v1)
          ∂(Measure.pi fun _ : Fin 2 => ν) := by
    intro v0 v1
    rw [← integral_finsetSum S (fun c _ => hint_box c v0 v1)]
    congr 1; funext u
    rw [hdec' u, Finset.sum_mul]

  have hL : ∫ y : F, (fun v : Fin 2 → F =>
        ∫ u : Fin 2 → F, Ψ u * ψ (u 1 * v 0 - u 0 * v 1) ∂(Measure.pi fun _ : Fin 2 => ν)) ![a, y] * ψ (b * y) ∂ν =
      ∑ c ∈ S, ∫ y : F, (fun v : Fin 2 → F =>
        ∫ u : Fin 2 → F, (Ψ c * (ind p N (c 0) (u 0) * ind p N (c 1) (u 1))) * ψ (u 1 * v 0 - u 0 * v 1)
          ∂(Measure.pi fun _ : Fin 2 => ν)) ![a, y] * ψ (b * y) ∂ν := by
    rw [← integral_finsetSum S]
    · congr 1; funext y
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hinner a y, Finset.sum_mul]
    · intro c _

      have hval : ∀ y : F, (fun v : Fin 2 → F =>
          ∫ u : Fin 2 → F, (Ψ c * (ind p N (c 0) (u 0) * ind p N (c 1) (u 1))) * ψ (u 1 * v 0 - u 0 * v 1)
            ∂(Measure.pi fun _ : Fin 2 => ν)) ![a, y] * ψ (b * y) =
          (Ψ c * ∫ x : F, ind p N (c 1) x * ψ (x * a) ∂ν) * tateFourier ψ ν (ind p N (c 0)) (-y) * ψ (b * y) := by
        intro y
        have h := swap_box_inner p N (c 0) (c 1) (Ψ c) a y
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [h]; ring
      simp_rw [hval]
      exact integrable_tateFourier_ind_neg_mul p N (c 0) b _

  have hR : ∫ y : F, Ψ ![b, y] * ψ (a * y) ∂ν =
      ∑ c ∈ S, ∫ y : F, (Ψ c * (ind p N (c 0) (![b, y] 0) * ind p N (c 1) (![b, y] 1))) * ψ (a * y) ∂ν := by
    rw [← integral_finsetSum S]
    · congr 1; funext y
      rw [hdec' ![b, y], Finset.sum_mul]
    · intro c _
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have hform : (fun y : F => Ψ c * (ind p N (c 0) b * ind p N (c 1) y) * ψ (a * y)) =
          fun y => (ballc p N (c 1)).indicator (fun y => Ψ c * ind p N (c 0) b * ψ (a * y)) y := by
        funext y
        unfold ind
        by_cases hy : y ∈ ballc p N (c 1)
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]; ring
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]; ring
      rw [hform, integrable_indicator_iff (measurableSet_ballc p N (c 1))]
      refine Measure.integrableOn_of_bounded (M := ‖Ψ c * ind p N (c 0) b‖) (isCompact_ballc p N (c 1)).measure_lt_top.ne ?_ ?_
      · exact (continuous_const.mul ((NumberField.StandardAddChar.continuous_psiLocal ℚ p).comp
          (continuous_const.mul continuous_id))).aestronglyMeasurable
      · refine Eventually.of_forall fun y => ?_
        rw [norm_mul]
        calc ‖Ψ c * ind p N (c 0) b‖ * ‖ψ (a * y)‖ ≤ ‖Ψ c * ind p N (c 0) b‖ * 1 := by
              gcongr; exact norm_psi_le_one p _
          _ = _ := mul_one _
  rw [hL, hR]
  exact Finset.sum_congr rfl fun c _ => swap_box p N (c 0) (c 1) (Ψ c) a b

end SwapD2R

end

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (Ψ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (hΨ : IsLocallyConstant Ψ ∧ HasCompactSupport Ψ)
    (a b : p.adicCompletion ℚ) :
    letI := localBorel ℚ p
    ∫ y : p.adicCompletion ℚ,
        (fun v : Fin 2 → p.adicCompletion ℚ =>
            ∫ u : Fin 2 → p.adicCompletion ℚ, Ψ u * NumberField.StandardAddChar.psiLocal ℚ p (u 1 * v 0 - u 0 * v 1)
              ∂(Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p)) ![a, y] *
          NumberField.StandardAddChar.psiLocal ℚ p (b * y) ∂(selfDualHaarAt ℚ p) =
      ∫ y : p.adicCompletion ℚ, Ψ ![b, y] * NumberField.StandardAddChar.psiLocal ℚ p (a * y) ∂(selfDualHaarAt ℚ p) :=
  SwapD2R.swap_main p Ψ hΨ a b

end S_LanglandsTunnell_TateLocal_integral_symplecticFourier_mul_psiLocal_eq_integral_swap_mul_psiLocal
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_integral_symplecticFourier_mul_psiLocal_eq_integral_swap_mul_psiLocal (solution)
