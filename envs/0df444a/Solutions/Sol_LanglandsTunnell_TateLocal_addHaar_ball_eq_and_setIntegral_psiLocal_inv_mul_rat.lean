-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.addHaar_ball_eq_and_setIntegral_psiLocal_inv_mul_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/8eeaa2e8-8eb4-5525-8b62-1a44924cbcc2

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_HaarQuotient
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_addHaar_ball_eq_and_setIntegral_psiLocal_inv_mul_rat
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open UnramifiedWhittaker
open NumberField.AdelicLevel

noncomputable section

namespace SlSJA

open scoped ENNReal NNReal Pointwise

variable (v : HeightOneSpectrum (𝓞 ℚ))

abbrev Fv : Type := v.adicCompletion ℚ

def ball (j : ℤ) : Set (Fv v) := {y : Fv v | Valued.v y ≤ WithZero.exp j}

theorem mem_ball {j : ℤ} {y : Fv v} : y ∈ ball v j ↔ Valued.v y ≤ WithZero.exp j := Iff.rfl

theorem zero_mem_ball (j : ℤ) : (0 : Fv v) ∈ ball v j := by
  rw [mem_ball, map_zero]; exact zero_le'

theorem add_mem_ball {j : ℤ} {a b : Fv v} (ha : a ∈ ball v j) (hb : b ∈ ball v j) : a + b ∈ ball v j := by
  show Valued.v (a + b) ≤ WithZero.exp j
  exact (Valuation.map_add _ _ _).trans (max_le ha hb)

theorem neg_mem_ball {j : ℤ} {a : Fv v} (ha : a ∈ ball v j) : -a ∈ ball v j := by
  rw [mem_ball, Valuation.map_neg]; exact ha

abbrev ϖu : (Fv v)ˣ := uniformizerUnit ℚ v

theorem v_ϖu : Valued.v ((ϖu v : (Fv v)ˣ) : Fv v) = WithZero.exp (-1 : ℤ) := valued_uniformizerUnit ℚ v

theorem v_ϖu_zpow (a : ℤ) : Valued.v (((ϖu v) ^ a : (Fv v)ˣ) : Fv v) = WithZero.exp (-a) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, v_ϖu]
  have hne : (WithZero.exp (-1 : ℤ)) ^ a ≠ 0 := zpow_ne_zero a WithZero.exp_ne_zero
  rw [← WithZero.exp_log hne, WithZero.log_zpow, WithZero.log_exp, smul_eq_mul, mul_neg_one]

theorem norm_eq_zpow {y : Fv v} {k : ℤ} (hy : Valued.v y = WithZero.exp k) :
    ‖y‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ k := by
  rw [NumberField.FinitePlace.norm_def, hy, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
    show (WithZero.unzero (WithZero.exp_ne_zero : (WithZero.exp k : WithZero (Multiplicative ℤ)) ≠ 0)).toAdd = k
      from rfl]
  push_cast
  rfl

theorem ball_eq_smul (j : ℤ) : ball v j = ((ϖu v) ^ (-j) : (Fv v)ˣ) • ball v 0 := by
  ext y
  constructor
  · intro hy
    refine ⟨(((ϖu v) ^ j : (Fv v)ˣ) : Fv v) * y, ?_, ?_⟩
    · show Valued.v ((((ϖu v) ^ j : (Fv v)ˣ) : Fv v) * y) ≤ WithZero.exp 0
      rw [map_mul, v_ϖu_zpow]
      rcases eq_or_ne y 0 with rfl | hy0
      · rw [map_zero, mul_zero]; exact zero_le'
      · have hvy : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
        rw [mem_ball, ← WithZero.exp_log hvy, WithZero.exp_le_exp] at hy
        rw [← WithZero.exp_log hvy, ← WithZero.exp_add, WithZero.exp_le_exp]
        omega
    · show ((ϖu v) ^ (-j) : (Fv v)ˣ) • ((((ϖu v) ^ j : (Fv v)ˣ) : Fv v) * y) = y
      rw [Units.smul_def, smul_eq_mul, ← mul_assoc, ← Units.val_mul, zpow_neg, inv_mul_cancel, Units.val_one, one_mul]
  · rintro ⟨z, hz, rfl⟩
    show Valued.v (((ϖu v) ^ (-j) : (Fv v)ˣ) • z) ≤ WithZero.exp j
    rw [Units.smul_def, smul_eq_mul, map_mul, v_ϖu_zpow, neg_neg]
    have hz' : Valued.v z ≤ WithZero.exp 0 := hz
    calc WithZero.exp j * Valued.v z ≤ WithZero.exp j * WithZero.exp 0 := mul_le_mul_right hz' _
      _ = WithZero.exp j := by rw [WithZero.exp_zero, mul_one]

theorem isCompact_ball_zero : IsCompact (ball v 0) := by
  have h : ball v 0 = Set.range ((↑) : v.adicCompletionIntegers ℚ → Fv v) := by
    rw [Subtype.range_coe]
    ext y
    rw [mem_ball, WithZero.exp_zero]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).symm
  rw [h]
  exact isCompact_range continuous_subtype_val

section Topology

theorem restrict_ne_zero {y : Fv v} (hy : y ≠ 0) :
    (Valued.v.restrict y : MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v : Valuation (Fv v) (WithZero (Multiplicative ℤ))))) ≠ 0 := by
  rw [Ne, Valuation.restrict_eq_zero_iff]
  exact (Valuation.ne_zero_iff _).2 hy

theorem ball_eq_restrict (j : ℤ) :
    ball v j = {x : Fv v | Valued.v.restrict x ≤ Valued.v.restrict ((((ϖu v) ^ (-j) : (Fv v)ˣ) : Fv v))} := by
  ext x
  rw [mem_ball, Set.mem_setOf_eq, ← not_lt, ← not_lt, Valuation.restrict_lt_iff, v_ϖu_zpow, neg_neg]

theorem isOpen_ball (j : ℤ) : IsOpen (ball v j) := by
  rw [ball_eq_restrict]
  exact Valued.isOpen_closedBall (R := Fv v) (restrict_ne_zero v (Units.ne_zero _))

theorem isClosed_ball (j : ℤ) : IsClosed (ball v j) := by
  rw [ball_eq_restrict]
  exact Valued.isClosed_closedBall (Fv v) _

end Topology

section Measure

variable [MeasurableSpace (Fv v)] [BorelSpace (Fv v)]

theorem measurableSet_ball (j : ℤ) : MeasurableSet (ball v j) := (isClosed_ball v j).measurableSet

theorem coe_modulus_eq_norm (x : Fv v) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]

theorem measure_ball (ν : Measure (Fv v)) [ν.IsAddHaarMeasure] (j : ℤ) :
    ν (ball v j) = (distribHaarChar (Fv v) ((ϖu v) ^ (-j)) : ℝ≥0∞) * ν (ball v 0) := by
  rw [ball_eq_smul, ← distribHaarChar_mul ν ((ϖu v) ^ (-j)) (ball v 0)]

theorem distribHaarChar_ϖu_zpow_toReal (j : ℤ) :
    ((distribHaarChar (Fv v) ((ϖu v) ^ (-j)) : ℝ≥0) : ℝ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ j := by
  rw [← modulus_coe_units, coe_modulus_eq_norm, norm_eq_zpow v (v_ϖu_zpow v (-j)), neg_neg]

theorem measure_ball_pos (ν : Measure (Fv v)) [ν.IsAddHaarMeasure] (j : ℤ) : 0 < ν (ball v j) :=
  (isOpen_ball v j).measure_pos ν ⟨0, zero_mem_ball v j⟩

theorem measure_ball_zero_lt_top (ν : Measure (Fv v)) [ν.IsAddHaarMeasure] : ν (ball v 0) < ⊤ :=
  (isCompact_ball_zero v).measure_lt_top

theorem measure_ball_lt_top (ν : Measure (Fv v)) [ν.IsAddHaarMeasure] (j : ℤ) : ν (ball v j) < ⊤ := by
  rw [measure_ball]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_ball_zero_lt_top v ν)

theorem measure_ball_toReal (ν : Measure (Fv v)) [ν.IsAddHaarMeasure] (j : ℤ) :
    (ν (ball v j)).toReal = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ j * (ν (ball v 0)).toReal := by
  rw [measure_ball, ENNReal.toReal_mul, ENNReal.coe_toReal, distribHaarChar_ϖu_zpow_toReal]

theorem psi_eq_one {x : Fv v} (hx : Valued.v x ≤ 1) : NumberField.StandardAddChar.psiLocal ℚ v x = 1 :=
  LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ v x
    ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr hx)

theorem exists_psi_ne_one : ∃ x : Fv v, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ NumberField.StandardAddChar.psiLocal ℚ v x ≠ 1 := by
  have h := (LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ v
    (NumberField.StandardAddChar.psiLocal ℚ v) ⟨0, fun x hx => psi_eq_one v (by rwa [WithZero.exp_zero] at hx)⟩
    (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ v)).2
  rwa [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat v, zero_add] at h

theorem setIntegral_ball_translate (ν : Measure (Fv v)) [ν.IsAddHaarMeasure] (j : ℤ) (h : Fv v → ℂ) {y₁ : Fv v}
    (hy₁ : y₁ ∈ ball v j) :
    ∫ y in ball v j, h (y₁ + y) ∂ν = ∫ y in ball v j, h y ∂ν := by
  rw [← integral_indicator (measurableSet_ball v j), ← integral_indicator (measurableSet_ball v j)]
  have e : (ball v j).indicator (fun y => h (y₁ + y)) = fun y => (ball v j).indicator h (y₁ + y) := by
    funext y
    by_cases hy : y ∈ ball v j
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (add_mem_ball v hy₁ hy)]
    · have hy' : y₁ + y ∉ ball v j := fun h' => hy (by
        have := add_mem_ball v (neg_mem_ball v hy₁) h'
        rwa [neg_add_cancel_left] at this)
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy']
  rw [e, integral_add_left_eq_self]

theorem setIntegral_psi (ν : Measure (Fv v)) [ν.IsAddHaarMeasure] (t : Fv v) (j : ℤ) :
    ∫ y in ball v j, (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ (t * y) ∂ν =
      if Valued.v t ≤ WithZero.exp (-j) then ((ν (ball v j)).toReal : ℂ) else 0 := by
  split_ifs with ht
  ·
    have hcongr : ∀ y ∈ ball v j, (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ (t * y) = (1 : ℂ) := by
      intro y hy
      rw [AddChar.inv_apply]
      apply psi_eq_one v
      rw [Valuation.map_neg, map_mul]
      calc Valued.v t * Valued.v y ≤ WithZero.exp (-j) * WithZero.exp j := mul_le_mul' ht hy
        _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    rw [setIntegral_congr_fun (measurableSet_ball v j) hcongr, setIntegral_const]
    show (ν (ball v j)).toReal • (1 : ℂ) = ((ν (ball v j)).toReal : ℂ)
    rw [Complex.real_smul, mul_one]
  ·
    push Not at ht
    have ht0 : Valued.v t ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' ht)
    have ht0' : t ≠ 0 := (Valuation.ne_zero_iff _).mp ht0
    have htl : -j + 1 ≤ WithZero.log (Valued.v t) := by
      rw [← WithZero.exp_log ht0, WithZero.exp_lt_exp] at ht; omega
    obtain ⟨x, hx, hxψ⟩ := exists_psi_ne_one v
    set y₁ : Fv v := -(x * t⁻¹) with hy₁
    have hy₁mem : y₁ ∈ ball v j := by
      rw [hy₁]
      apply neg_mem_ball
      show Valued.v (x * t⁻¹) ≤ WithZero.exp j
      rw [map_mul, map_inv₀]
      rcases eq_or_ne x 0 with rfl | hx0
      · rw [map_zero, zero_mul]; exact zero_le'
      · have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
        rw [← WithZero.exp_log hvx, WithZero.exp_le_exp] at hx
        rw [← WithZero.exp_log hvx, ← WithZero.exp_log ht0, ← WithZero.exp_neg, ← WithZero.exp_add, WithZero.exp_le_exp]
        omega
    have hty₁ : (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ (t * y₁) ≠ 1 := by
      rw [AddChar.inv_apply, hy₁, mul_neg, neg_neg, mul_comm, inv_mul_cancel_right₀ ht0']
      exact hxψ
    have hmul : (∫ y in ball v j, (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ (t * y) ∂ν) =
        (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ (t * y₁) *
          ∫ y in ball v j, (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ (t * y) ∂ν := by
      calc (∫ y in ball v j, (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ (t * y) ∂ν)
          = ∫ y in ball v j, (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ (t * (y₁ + y)) ∂ν :=
            (setIntegral_ball_translate v ν j (fun y => (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ (t * y)) hy₁mem).symm
        _ = ∫ y in ball v j, (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ (t * y₁) *
              (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ (t * y) ∂ν := by
            simp only [mul_add, AddChar.map_add_eq_mul]
        _ = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ (t * y₁) *
              ∫ y in ball v j, (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ (t * y) ∂ν := integral_const_mul _ _
    have : (1 - (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ (t * y₁)) *
        (∫ y in ball v j, (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ (t * y) ∂ν) = 0 := by
      rw [sub_mul, one_mul, ← hmul, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hty₁.symm)

end Measure

end SlSJA

end

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ v
    ∀ (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      (∀ j : ℤ, 0 < ν {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp j} ∧
        ν {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp j} < ⊤ ∧
        (ν {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp j}).toReal =
          (Ideal.absNorm v.asIdeal : ℝ) ^ j * (ν {y : v.adicCompletion ℚ | Valued.v y ≤ 1}).toReal) ∧
      (∀ (t : v.adicCompletion ℚ) (j : ℤ),
        ∫ y in {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp j},
            (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ (t * y) ∂ν =
          if Valued.v t ≤ WithZero.exp (-j)
            then ((ν {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp j}).toReal : ℂ) else 0) := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  intro ν _
  have hb : ∀ j : ℤ, {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp j} = SlSJA.ball v j := fun j => rfl
  have hb0 : {y : v.adicCompletion ℚ | Valued.v y ≤ 1} = SlSJA.ball v 0 := by
    ext y; rw [SlSJA.mem_ball, WithZero.exp_zero]; exact Iff.rfl
  refine ⟨fun j => ⟨SlSJA.measure_ball_pos v ν j, SlSJA.measure_ball_lt_top v ν j, ?_⟩, fun t j => SlSJA.setIntegral_psi v ν t j⟩
  rw [hb0]
  exact SlSJA.measure_ball_toReal v ν j

end S_LanglandsTunnell_TateLocal_addHaar_ball_eq_and_setIntegral_psiLocal_inv_mul_rat
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_addHaar_ball_eq_and_setIntegral_psiLocal_inv_mul_rat (solution)
