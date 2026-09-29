-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.integrable_cellSectionOf_antidiagonal3_mul_upperUnipotent3_mul_of_norm_eq_rpow_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b60f71a8-e67d-577a-aadb-cc8986c0c4e9

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Theorems.Thm_LanglandsTunnell_TateLocal_measureReal_setOf_valued_le_exp
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_psiLocal_and_inv_eq_jacquetValue_and_eq_sum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_integrable_cellSectionOf_antidiagonal3_mul_upperUnipotent3_mul_of_norm_eq_rpow_of_lt
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace LTGKRankTwo

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction Filter Topology

open scoped ENNReal NNReal

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => HeightOneSpectrum.adicCompletion ℚ v

section Norms

def qv : ℝ := (Ideal.absNorm v.asIdeal : ℝ)

theorem one_lt_qv : 1 < qv v := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm v
  unfold qv
  exact_mod_cast this

theorem qv_pos : 0 < qv v := lt_trans zero_lt_one (one_lt_qv v)

theorem exists_norm_eq_zpow {x : F} (hx : x ≠ 0) :
    ∃ k : ℤ, ‖x‖ = qv v ^ k ∧ (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp k := by
  have hv0 : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  refine ⟨Multiplicative.toAdd (WithZero.unzero hv0), ?_, ?_⟩
  · rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv0]
    push_cast
    rfl
  · conv_lhs => rw [← WithZero.coe_unzero hv0]
    rfl

theorem norm_le_zpow_iff (x : F) (k : ℤ) : ‖x‖ ≤ qv v ^ k ↔ Valued.v x ≤ WithZero.exp k := by
  by_cases hx : x = 0
  · subst hx
    simp only [norm_zero, map_zero, zero_le', iff_true]
    exact zpow_nonneg (qv_pos v).le _
  · obtain ⟨m, hm, hvm⟩ := exists_norm_eq_zpow v hx
    rw [hm, hvm, zpow_le_zpow_iff_right₀ (one_lt_qv v), WithZero.exp_le_exp]

theorem closedBall_zero_eq (k : ℤ) :
    Metric.closedBall (0 : F) (qv v ^ k) = {x : F | Valued.v x ≤ WithZero.exp k} := by
  ext x
  rw [Metric.mem_closedBall, dist_zero_right, Set.mem_setOf_eq, norm_le_zpow_iff]

end Norms

section RankOne

variable [MeasurableSpace (HeightOneSpectrum.adicCompletion ℚ v)] [BorelSpace (HeightOneSpectrum.adicCompletion ℚ v)]
variable (μ : Measure (HeightOneSpectrum.adicCompletion ℚ v)) [μ.IsAddHaarMeasure]

def ints : Set F := (v.adicCompletionIntegers ℚ : Set F)

theorem isCompact_ints : IsCompact (ints v) :=
  isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers ℚ) from inferInstance)

theorem isOpen_ints : IsOpen (ints v) := Valued.isOpen_valuationSubring _

theorem zero_mem_ints : (0 : F) ∈ ints v := (v.adicCompletionIntegers ℚ).zero_mem

theorem measureReal_ints_pos : 0 < μ.real (ints v) := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos ((isOpen_ints v).measure_pos μ ⟨0, zero_mem_ints v⟩).ne'
    ((isCompact_ints v).measure_lt_top).ne

theorem measure_closedBall_zero (k : ℤ) :
    μ (Metric.closedBall (0 : F) (qv v ^ k)) = ENNReal.ofReal (qv v ^ k * μ.real (ints v)) := by
  have hreal : μ.real (Metric.closedBall (0 : F) (qv v ^ k)) = qv v ^ k * μ.real (ints v) := by
    rw [closedBall_zero_eq]
    exact measureReal_setOf_valued_le_exp ℚ v μ k
  have hpos : 0 < μ.real (Metric.closedBall (0 : F) (qv v ^ k)) := by
    rw [hreal]
    exact mul_pos (zpow_pos (qv_pos v) k) (measureReal_ints_pos v μ)
  have hne : μ (Metric.closedBall (0 : F) (qv v ^ k)) ≠ ∞ := by
    intro h
    rw [measureReal_def, h, ENNReal.toReal_top] at hpos
    exact lt_irrefl _ hpos
  rw [← ENNReal.ofReal_toReal hne, ← measureReal_def, hreal]

theorem measure_closedBall (c : F) (k : ℤ) :
    μ (Metric.closedBall c (qv v ^ k)) = ENNReal.ofReal (qv v ^ k * μ.real (ints v)) := by
  have hset : Metric.closedBall c (qv v ^ k) = (fun y => -c + y) ⁻¹' Metric.closedBall (0 : F) (qv v ^ k) := by
    ext y
    simp only [Metric.mem_closedBall, dist_eq_norm, Set.mem_preimage, sub_zero]
    rw [neg_add_eq_sub]
  rw [hset, measure_preimage_add, measure_closedBall_zero]

def geomZ (s : ℝ) : ℝ≥0∞ := ∑' k : ℕ, ENNReal.ofReal (qv v ^ (-s)) ^ k

theorem geomZ_lt_top {s : ℝ} (hs : 0 < s) : geomZ v s < ∞ := by
  unfold geomZ
  rw [ENNReal.tsum_geometric, ENNReal.inv_lt_top, tsub_pos_iff_lt, ENNReal.ofReal_lt_one]
  exact Real.rpow_lt_one_of_one_lt_of_neg (one_lt_qv v) (neg_lt_zero.mpr hs)

def R1 (s : ℝ) : ℝ≥0∞ := ENNReal.ofReal (μ.real (ints v)) * geomZ v s

theorem R1_lt_top {s : ℝ} (hs : 0 < s) : R1 v μ s < ∞ :=
  ENNReal.mul_lt_top ENNReal.ofReal_lt_top (geomZ_lt_top v hs)

theorem scal (s : ℝ) (k : ℕ) (j : ℤ) :
    (qv v ^ k : ℝ) ^ (-(s + 1)) * qv v ^ ((k : ℤ) - j) = (qv v ^ (-s)) ^ k * (qv v ^ j)⁻¹ := by
  have hq := qv_pos v
  rw [← Real.rpow_natCast (qv v) k, ← Real.rpow_mul hq.le, ← Real.rpow_intCast (qv v) ((k : ℤ) - j),
    ← Real.rpow_add hq, ← Real.rpow_natCast (qv v ^ (-s)) k, ← Real.rpow_mul hq.le,
    ← Real.rpow_intCast (qv v) j, ← Real.rpow_neg hq.le, ← Real.rpow_add hq]
  congr 1
  push_cast
  ring

theorem pointwise (s : ℝ) (c : F) (j : ℤ) (y : F) :
    ENNReal.ofReal ((max 1 (qv v ^ j * ‖y - c‖)) ^ (-(s + 1))) ≤
      ∑' k : ℕ, (Metric.closedBall c (qv v ^ ((k : ℤ) - j))).indicator
        (fun _ => ENNReal.ofReal ((qv v ^ k : ℝ) ^ (-(s + 1)))) y := by
  have hq := qv_pos v
  by_cases hle : qv v ^ j * ‖y - c‖ ≤ 1
  · have hmax : max 1 (qv v ^ j * ‖y - c‖) = 1 := max_eq_left hle
    have hmem : y ∈ Metric.closedBall c (qv v ^ (((0 : ℕ) : ℤ) - j)) := by
      rw [Metric.mem_closedBall, dist_eq_norm, Nat.cast_zero, zero_sub, zpow_neg, ← one_div,
        le_div_iff₀' (zpow_pos hq j)]
      exact hle
    refine le_trans ?_ (ENNReal.le_tsum 0)
    rw [Set.indicator_of_mem hmem, hmax, pow_zero, Real.one_rpow]
  · push Not at hle
    have hyc : y - c ≠ 0 := by
      intro h
      rw [h, norm_zero, mul_zero] at hle
      exact absurd hle (not_lt.mpr zero_le_one)
    obtain ⟨m, hm, -⟩ := exists_norm_eq_zpow v hyc
    have hjm : 0 < j + m := by
      rw [hm, ← zpow_add₀ hq.ne'] at hle
      exact (one_lt_zpow_iff_right₀ (one_lt_qv v)).mp hle
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = j + m := ⟨(j + m).toNat, Int.toNat_of_nonneg hjm.le⟩
    have hmax : max 1 (qv v ^ j * ‖y - c‖) = qv v ^ k := by
      rw [max_eq_right hle.le, hm, ← zpow_add₀ hq.ne', ← hk, zpow_natCast]
    have hmem : y ∈ Metric.closedBall c (qv v ^ ((k : ℤ) - j)) := by
      rw [Metric.mem_closedBall, dist_eq_norm, hm, hk, show j + m - j = m by ring]
    refine le_trans ?_ (ENNReal.le_tsum k)
    rw [Set.indicator_of_mem hmem, hmax]

theorem rankOne (s : ℝ) (c : F) (j : ℤ) :
    ∫⁻ y, ENNReal.ofReal ((max 1 (qv v ^ j * ‖y - c‖)) ^ (-(s + 1))) ∂μ ≤
      ENNReal.ofReal ((qv v ^ j)⁻¹) * R1 v μ s := by
  have hq := qv_pos v
  calc ∫⁻ y, ENNReal.ofReal ((max 1 (qv v ^ j * ‖y - c‖)) ^ (-(s + 1))) ∂μ
      ≤ ∫⁻ y, ∑' k : ℕ, (Metric.closedBall c (qv v ^ ((k : ℤ) - j))).indicator
          (fun _ => ENNReal.ofReal ((qv v ^ k : ℝ) ^ (-(s + 1)))) y ∂μ :=
        lintegral_mono fun y => pointwise v s c j y
    _ = ∑' k : ℕ, ∫⁻ y, (Metric.closedBall c (qv v ^ ((k : ℤ) - j))).indicator
          (fun _ => ENNReal.ofReal ((qv v ^ k : ℝ) ^ (-(s + 1)))) y ∂μ :=
        lintegral_tsum fun k => (measurable_const.indicator Metric.isClosed_closedBall.measurableSet).aemeasurable
    _ = ∑' k : ℕ, ENNReal.ofReal ((qv v ^ k : ℝ) ^ (-(s + 1))) * μ (Metric.closedBall c (qv v ^ ((k : ℤ) - j))) := by
        congr 1
        funext k
        rw [lintegral_indicator_const Metric.isClosed_closedBall.measurableSet]
    _ = ∑' k : ℕ, ENNReal.ofReal (qv v ^ (-s)) ^ k * ENNReal.ofReal ((qv v ^ j)⁻¹ * μ.real (ints v)) := by
        congr 1
        funext k
        rw [measure_closedBall, ← ENNReal.ofReal_mul (Real.rpow_nonneg (pow_nonneg hq.le k) _), ← mul_assoc,
          scal, mul_assoc, ENNReal.ofReal_mul (pow_nonneg (Real.rpow_nonneg hq.le _) k),
          ENNReal.ofReal_pow (Real.rpow_nonneg hq.le _)]
    _ = geomZ v s * ENNReal.ofReal ((qv v ^ j)⁻¹ * μ.real (ints v)) := ENNReal.tsum_mul_right
    _ = ENNReal.ofReal ((qv v ^ j)⁻¹) * R1 v μ s := by
        unfold R1
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr (zpow_nonneg hq.le j))]
        ring

end RankOne

section Kernel

def sh (s r : ℝ) : ℝ := (max 1 r) ^ (-(s + 1))

theorem sh_nonneg (s r : ℝ) : 0 ≤ sh s r :=
  Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _

theorem sh_antitone {s : ℝ} (hs : 0 < s) {r r' : ℝ} (h : r ≤ r') : sh s r' ≤ sh s r :=
  Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (le_max_left _ _)) (max_le_max le_rfl h) (by linarith)

theorem continuous_sh (s : ℝ) : Continuous (sh s) :=
  (continuous_const.max continuous_id).rpow_const fun r =>
    Or.inl (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'

def kerA (b : ℝ) (x z : F) : ℝ≥0∞ := ENNReal.ofReal (sh b (max ‖x‖ ‖z‖))

def kerB (a : ℝ) (x y z : F) : ℝ≥0∞ := ENNReal.ofReal (sh a (max ‖y‖ ‖z - x * y‖))

def ker (a b : ℝ) (p : F × F × F) : ℝ≥0∞ := kerA v b p.1 p.2.2 * kerB v a p.1 p.2.1 p.2.2

variable [MeasurableSpace (HeightOneSpectrum.adicCompletion ℚ v)] [BorelSpace (HeightOneSpectrum.adicCompletion ℚ v)]

theorem measurable_ker (a b : ℝ) : Measurable (ker v a b) := by
  have hA : Continuous fun p : F × F × F => sh b (max ‖p.1‖ ‖p.2.2‖) :=
    (continuous_sh b).comp ((continuous_norm.comp continuous_fst).max
      (continuous_norm.comp (continuous_snd.comp continuous_snd)))
  have hB : Continuous fun p : F × F × F => sh a (max ‖p.2.1‖ ‖p.2.2 - p.1 * p.2.1‖) :=
    (continuous_sh a).comp ((continuous_norm.comp (continuous_fst.comp continuous_snd)).max
      (continuous_norm.comp ((continuous_snd.comp continuous_snd).sub
        (continuous_fst.mul (continuous_fst.comp continuous_snd)))))
  exact (ENNReal.measurable_ofReal.comp hA.measurable).mul (ENNReal.measurable_ofReal.comp hB.measurable)

variable (μ : Measure (HeightOneSpectrum.adicCompletion ℚ v)) [μ.IsAddHaarMeasure]

theorem inner_bound {a : ℝ} (ha : 0 < a) (x z : F) :
    ∫⁻ y, kerB v a x y z ∂μ ≤ ENNReal.ofReal ((max 1 ‖x‖)⁻¹) * R1 v μ a := by
  by_cases hx : ‖x‖ ≤ 1
  · have h1 : max 1 ‖x‖ = 1 := max_eq_left hx
    calc ∫⁻ y, kerB v a x y z ∂μ
        ≤ ∫⁻ y, ENNReal.ofReal ((max 1 (qv v ^ (0 : ℤ) * ‖y - 0‖)) ^ (-(a + 1))) ∂μ := by
          refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
          rw [zpow_zero, one_mul, sub_zero]
          exact sh_antitone ha (le_max_left _ _)
      _ ≤ ENNReal.ofReal ((qv v ^ (0 : ℤ))⁻¹) * R1 v μ a := rankOne v μ _ 0 0
      _ = ENNReal.ofReal ((max 1 ‖x‖)⁻¹) * R1 v μ a := by rw [zpow_zero, h1]
  · push Not at hx
    have hx0 : x ≠ 0 := fun h => by
      rw [h, norm_zero] at hx
      exact absurd hx (not_lt.mpr zero_le_one)
    obtain ⟨j, hj, -⟩ := exists_norm_eq_zpow v hx0
    have h1 : max 1 ‖x‖ = qv v ^ j := by rw [max_eq_right hx.le, hj]
    calc ∫⁻ y, kerB v a x y z ∂μ
        ≤ ∫⁻ y, ENNReal.ofReal ((max 1 (qv v ^ j * ‖y - z / x‖)) ^ (-(a + 1))) ∂μ := by
          refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal (sh_antitone ha ?_)
          rw [← hj, ← norm_mul, mul_sub, mul_div_cancel₀ _ hx0, norm_sub_rev]
          exact le_max_right _ _
      _ ≤ ENNReal.ofReal ((qv v ^ j)⁻¹) * R1 v μ a := rankOne v μ _ _ j
      _ = ENNReal.ofReal ((max 1 ‖x‖)⁻¹) * R1 v μ a := by rw [h1]

theorem middle_bound {b : ℝ} (hb : 0 < b) (x : F) :
    ∫⁻ z, kerA v b x z ∂μ ≤ ENNReal.ofReal ((max 1 ‖x‖) ^ (-b)) * R1 v μ b := by
  have hq := qv_pos v
  obtain ⟨j, hj⟩ : ∃ j : ℤ, max 1 ‖x‖ = qv v ^ j := by
    by_cases hx : ‖x‖ ≤ 1
    · exact ⟨0, by rw [max_eq_left hx, zpow_zero]⟩
    · push Not at hx
      have hx0 : x ≠ 0 := fun h => by
        rw [h, norm_zero] at hx
        exact absurd hx (not_lt.mpr zero_le_one)
      obtain ⟨j, hj', -⟩ := exists_norm_eq_zpow v hx0
      exact ⟨j, by rw [max_eq_right hx.le, hj']⟩
  have hX : 0 < max 1 ‖x‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hpt : ∀ z : F, kerA v b x z =
      ENNReal.ofReal ((max 1 ‖x‖) ^ (-(b + 1))) *
        ENNReal.ofReal ((max 1 (qv v ^ (-j) * ‖z - 0‖)) ^ (-(b + 1))) := by
    intro z
    rw [kerA, sh, ← ENNReal.ofReal_mul (Real.rpow_nonneg hX.le _),
      ← Real.mul_rpow hX.le (le_trans zero_le_one (le_max_left _ _))]
    congr 2
    rw [sub_zero, ← max_assoc, zpow_neg, ← hj, mul_max_of_nonneg _ _ hX.le, mul_one, ← mul_assoc,
      mul_inv_cancel₀ hX.ne', one_mul]
  calc ∫⁻ z, kerA v b x z ∂μ
      = ∫⁻ z, ENNReal.ofReal ((max 1 ‖x‖) ^ (-(b + 1))) *
          ENNReal.ofReal ((max 1 (qv v ^ (-j) * ‖z - 0‖)) ^ (-(b + 1))) ∂μ := lintegral_congr hpt
    _ = ENNReal.ofReal ((max 1 ‖x‖) ^ (-(b + 1))) *
          ∫⁻ z, ENNReal.ofReal ((max 1 (qv v ^ (-j) * ‖z - 0‖)) ^ (-(b + 1))) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((max 1 ‖x‖) ^ (-(b + 1))) * (ENNReal.ofReal ((qv v ^ (-j))⁻¹) * R1 v μ b) :=
        mul_le_mul_right (rankOne v μ _ 0 (-j)) _
    _ = ENNReal.ofReal ((max 1 ‖x‖) ^ (-b)) * R1 v μ b := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hX.le _), zpow_neg, inv_inv, ← hj]
        congr 2
        rw [show -(b + 1) = -b + (-1) by ring, Real.rpow_add hX, Real.rpow_neg_one, mul_assoc,
          inv_mul_cancel₀ hX.ne', mul_one]

theorem lintegral_ker_lt_top {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫⁻ p, ker v a b p ∂(μ.prod (μ.prod μ)) < ∞ := by
  have hRa := R1_lt_top v μ ha
  have hRb := R1_lt_top v μ hb
  have h1 : ∫⁻ p, ker v a b p ∂(μ.prod (μ.prod μ)) = ∫⁻ x, ∫⁻ q, ker v a b (x, q) ∂(μ.prod μ) ∂μ :=
    lintegral_prod _ (measurable_ker v a b).aemeasurable
  have h2 : ∀ x, ∫⁻ q, ker v a b (x, q) ∂(μ.prod μ) = ∫⁻ z, ∫⁻ y, ker v a b (x, (y, z)) ∂μ ∂μ := fun x =>
    lintegral_prod_symm _ ((measurable_ker v a b).comp measurable_prodMk_left).aemeasurable
  have h3 : ∀ x z, ∫⁻ y, ker v a b (x, (y, z)) ∂μ ≤
      kerA v b x z * (ENNReal.ofReal ((max 1 ‖x‖)⁻¹) * R1 v μ a) := by
    intro x z
    show ∫⁻ y, kerA v b x z * kerB v a x y z ∂μ ≤ _
    rw [lintegral_const_mul' (kerA v b x z) (fun y => kerB v a x y z) ENNReal.ofReal_ne_top]
    exact mul_le_mul_right (inner_bound v μ ha x z) _
  have h4 : ∀ x, ∫⁻ z, ∫⁻ y, ker v a b (x, (y, z)) ∂μ ∂μ ≤
      ENNReal.ofReal ((max 1 ‖x‖) ^ (-b)) * R1 v μ b * (ENNReal.ofReal ((max 1 ‖x‖)⁻¹) * R1 v μ a) := by
    intro x
    calc ∫⁻ z, ∫⁻ y, ker v a b (x, (y, z)) ∂μ ∂μ
        ≤ ∫⁻ z, kerA v b x z * (ENNReal.ofReal ((max 1 ‖x‖)⁻¹) * R1 v μ a) ∂μ := lintegral_mono (h3 x)
      _ = (∫⁻ z, kerA v b x z ∂μ) * (ENNReal.ofReal ((max 1 ‖x‖)⁻¹) * R1 v μ a) :=
          lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRa.ne)
      _ ≤ _ := mul_le_mul_left (middle_bound v μ hb x) _
  have h5 : ∀ x : F, ENNReal.ofReal ((max 1 ‖x‖) ^ (-b)) * R1 v μ b *
      (ENNReal.ofReal ((max 1 ‖x‖)⁻¹) * R1 v μ a) =
        (R1 v μ b * R1 v μ a) * ENNReal.ofReal ((max 1 (qv v ^ (0 : ℤ) * ‖x - 0‖)) ^ (-(b + 1))) := by
    intro x
    have hX : 0 < max 1 ‖x‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
    rw [zpow_zero, one_mul, sub_zero,
      show (max 1 ‖x‖) ^ (-(b + 1)) = (max 1 ‖x‖) ^ (-b) * (max 1 ‖x‖)⁻¹ by
        rw [show -(b + 1) = -b + (-1) by ring, Real.rpow_add hX, Real.rpow_neg_one],
      ENNReal.ofReal_mul (Real.rpow_nonneg hX.le _)]
    ring
  calc ∫⁻ p, ker v a b p ∂(μ.prod (μ.prod μ))
      = ∫⁻ x, ∫⁻ z, ∫⁻ y, ker v a b (x, (y, z)) ∂μ ∂μ ∂μ := by rw [h1]; exact lintegral_congr h2
    _ ≤ ∫⁻ x, (R1 v μ b * R1 v μ a) *
          ENNReal.ofReal ((max 1 (qv v ^ (0 : ℤ) * ‖x - 0‖)) ^ (-(b + 1))) ∂μ :=
        lintegral_mono fun x => (h4 x).trans_eq (h5 x)
    _ = (R1 v μ b * R1 v μ a) *
          ∫⁻ x, ENNReal.ofReal ((max 1 (qv v ^ (0 : ℤ) * ‖x - 0‖)) ^ (-(b + 1))) ∂μ :=
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top hRb.ne hRa.ne)
    _ ≤ (R1 v μ b * R1 v μ a) * (ENNReal.ofReal ((qv v ^ (0 : ℤ))⁻¹) * R1 v μ b) :=
        mul_le_mul_right (rankOne v μ _ 0 0) _
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hRb hRa) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hRb)

end Kernel

section Invariants

variable {v}

def bottomMax (A : Matrix (Fin 3) (Fin 3) F) : ℝ := max ‖A 2 0‖ (max ‖A 2 1‖ ‖A 2 2‖)

def m01 (A : Matrix (Fin 3) (Fin 3) F) : F := A 1 0 * A 2 1 - A 1 1 * A 2 0

def m02 (A : Matrix (Fin 3) (Fin 3) F) : F := A 1 0 * A 2 2 - A 1 2 * A 2 0

def m12 (A : Matrix (Fin 3) (Fin 3) F) : F := A 1 1 * A 2 2 - A 1 2 * A 2 1

def minorMax (A : Matrix (Fin 3) (Fin 3) F) : ℝ := max ‖m01 A‖ (max ‖m02 A‖ ‖m12 A‖)

def entryBound (G : Matrix (Fin 3) (Fin 3) F) : ℝ := 1 + ∑ i, ∑ j, ‖G i j‖

theorem one_le_entryBound (G : Matrix (Fin 3) (Fin 3) F) : 1 ≤ entryBound G := by
  unfold entryBound
  have : 0 ≤ ∑ i, ∑ j, ‖G i j‖ := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  linarith

theorem entryBound_pos (G : Matrix (Fin 3) (Fin 3) F) : 0 < entryBound G :=
  lt_of_lt_of_le one_pos (one_le_entryBound G)

theorem norm_entry_le_entryBound (G : Matrix (Fin 3) (Fin 3) F) (i j : Fin 3) : ‖G i j‖ ≤ entryBound G := by
  unfold entryBound
  have h1 : ‖G i j‖ ≤ ∑ j', ‖G i j'‖ :=
    Finset.single_le_sum (f := fun j' => ‖G i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  have h2 : (∑ j', ‖G i j'‖) ≤ ∑ i', ∑ j', ‖G i' j'‖ :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖G i' j'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  linarith

theorem bottomMax_nonneg (A : Matrix (Fin 3) (Fin 3) F) : 0 ≤ bottomMax A :=
  le_trans (norm_nonneg _) (le_max_left _ _)

theorem minorMax_nonneg (A : Matrix (Fin 3) (Fin 3) F) : 0 ≤ minorMax A :=
  le_trans (norm_nonneg _) (le_max_left _ _)

theorem det_eq_top_expansion (A : Matrix (Fin 3) (Fin 3) F) :
    A.det = A 0 0 * m12 A - A 0 1 * m02 A + A 0 2 * m01 A := by
  simp only [Matrix.det_fin_three, m01, m02, m12]
  ring

theorem bottomMax_pos {A : Matrix (Fin 3) (Fin 3) F} (hA : A.det ≠ 0) : 0 < bottomMax A := by
  by_contra h
  have h0 : bottomMax A = 0 := le_antisymm (not_lt.mp h) (bottomMax_nonneg A)
  have e0 : A 2 0 = 0 := norm_eq_zero.mp (le_antisymm (h0 ▸ le_max_left _ _) (norm_nonneg _))
  have e1 : A 2 1 = 0 :=
    norm_eq_zero.mp (le_antisymm (h0 ▸ (le_max_left _ _).trans (le_max_right _ _)) (norm_nonneg _))
  have e2 : A 2 2 = 0 :=
    norm_eq_zero.mp (le_antisymm (h0 ▸ (le_max_right _ _).trans (le_max_right _ _)) (norm_nonneg _))
  apply hA
  rw [Matrix.det_fin_three, e0, e1, e2]
  ring

theorem minorMax_pos {A : Matrix (Fin 3) (Fin 3) F} (hA : A.det ≠ 0) : 0 < minorMax A := by
  by_contra h
  have h0 : minorMax A = 0 := le_antisymm (not_lt.mp h) (minorMax_nonneg A)
  have e0 : m01 A = 0 := norm_eq_zero.mp (le_antisymm (h0 ▸ le_max_left _ _) (norm_nonneg _))
  have e1 : m02 A = 0 :=
    norm_eq_zero.mp (le_antisymm (h0 ▸ (le_max_left _ _).trans (le_max_right _ _)) (norm_nonneg _))
  have e2 : m12 A = 0 :=
    norm_eq_zero.mp (le_antisymm (h0 ▸ (le_max_right _ _).trans (le_max_right _ _)) (norm_nonneg _))
  apply hA
  rw [det_eq_top_expansion, e0, e1, e2]
  ring

theorem bottom_mul (A G : Matrix (Fin 3) (Fin 3) F) (j : Fin 3) :
    (A * G) 2 j = A 2 0 * G 0 j + A 2 1 * G 1 j + A 2 2 * G 2 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem norm_bottom_mul_le (A G : Matrix (Fin 3) (Fin 3) F) (j : Fin 3) :
    ‖(A * G) 2 j‖ ≤ 3 * entryBound G * bottomMax A := by
  rw [bottom_mul]
  have hE := entryBound_pos G
  have hb := bottomMax_nonneg A
  have h0 : ‖A 2 0 * G 0 j‖ ≤ bottomMax A * entryBound G := by
    rw [norm_mul]
    exact mul_le_mul (le_max_left _ _) (norm_entry_le_entryBound G 0 j) (norm_nonneg _) hb
  have h1 : ‖A 2 1 * G 1 j‖ ≤ bottomMax A * entryBound G := by
    rw [norm_mul]
    exact mul_le_mul ((le_max_left _ _).trans (le_max_right _ _)) (norm_entry_le_entryBound G 1 j)
      (norm_nonneg _) hb
  have h2 : ‖A 2 2 * G 2 j‖ ≤ bottomMax A * entryBound G := by
    rw [norm_mul]
    exact mul_le_mul ((le_max_right _ _).trans (le_max_right _ _)) (norm_entry_le_entryBound G 2 j)
      (norm_nonneg _) hb
  calc ‖A 2 0 * G 0 j + A 2 1 * G 1 j + A 2 2 * G 2 j‖
      ≤ ‖A 2 0 * G 0 j‖ + ‖A 2 1 * G 1 j‖ + ‖A 2 2 * G 2 j‖ := norm_add₃_le
    _ ≤ bottomMax A * entryBound G + bottomMax A * entryBound G + bottomMax A * entryBound G := by linarith
    _ = 3 * entryBound G * bottomMax A := by ring

theorem bottomMax_mul_le (A G : Matrix (Fin 3) (Fin 3) F) : bottomMax (A * G) ≤ 3 * entryBound G * bottomMax A :=
  max_le (norm_bottom_mul_le A G 0) (max_le (norm_bottom_mul_le A G 1) (norm_bottom_mul_le A G 2))

theorem m01_mul (A G : Matrix (Fin 3) (Fin 3) F) :
    m01 (A * G) = m01 A * (G 0 0 * G 1 1 - G 1 0 * G 0 1) + m02 A * (G 0 0 * G 2 1 - G 2 0 * G 0 1)
      + m12 A * (G 1 0 * G 2 1 - G 2 0 * G 1 1) := by
  simp only [m01, m02, m12, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem m02_mul (A G : Matrix (Fin 3) (Fin 3) F) :
    m02 (A * G) = m01 A * (G 0 0 * G 1 2 - G 1 0 * G 0 2) + m02 A * (G 0 0 * G 2 2 - G 2 0 * G 0 2)
      + m12 A * (G 1 0 * G 2 2 - G 2 0 * G 1 2) := by
  simp only [m01, m02, m12, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem m12_mul (A G : Matrix (Fin 3) (Fin 3) F) :
    m12 (A * G) = m01 A * (G 0 1 * G 1 2 - G 1 1 * G 0 2) + m02 A * (G 0 1 * G 2 2 - G 2 1 * G 0 2)
      + m12 A * (G 1 1 * G 2 2 - G 2 1 * G 1 2) := by
  simp only [m01, m02, m12, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem norm_twoMinor_le (G : Matrix (Fin 3) (Fin 3) F) (i i' k k' : Fin 3) :
    ‖G i k * G i' k' - G i' k * G i k'‖ ≤ 2 * entryBound G ^ 2 := by
  have hE := entryBound_pos G
  have h := norm_entry_le_entryBound G
  calc ‖G i k * G i' k' - G i' k * G i k'‖
      ≤ ‖G i k * G i' k'‖ + ‖G i' k * G i k'‖ := norm_sub_le _ _
    _ ≤ entryBound G * entryBound G + entryBound G * entryBound G := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul (h i k) (h i' k') (norm_nonneg _) hE.le)
          (mul_le_mul (h i' k) (h i k') (norm_nonneg _) hE.le)
    _ = 2 * entryBound G ^ 2 := by ring

theorem norm_combination_le (A G : Matrix (Fin 3) (Fin 3) F) (t₁ t₂ t₃ : F)
    (h₁ : ‖t₁‖ ≤ 2 * entryBound G ^ 2) (h₂ : ‖t₂‖ ≤ 2 * entryBound G ^ 2) (h₃ : ‖t₃‖ ≤ 2 * entryBound G ^ 2) :
    ‖m01 A * t₁ + m02 A * t₂ + m12 A * t₃‖ ≤ 6 * entryBound G ^ 2 * minorMax A := by
  have hM := minorMax_nonneg A
  have hE2 : 0 ≤ 2 * entryBound G ^ 2 := by positivity
  have k₁ : ‖m01 A * t₁‖ ≤ minorMax A * (2 * entryBound G ^ 2) := by
    rw [norm_mul]
    exact mul_le_mul (le_max_left _ _) h₁ (norm_nonneg _) hM
  have k₂ : ‖m02 A * t₂‖ ≤ minorMax A * (2 * entryBound G ^ 2) := by
    rw [norm_mul]
    exact mul_le_mul ((le_max_left _ _).trans (le_max_right _ _)) h₂ (norm_nonneg _) hM
  have k₃ : ‖m12 A * t₃‖ ≤ minorMax A * (2 * entryBound G ^ 2) := by
    rw [norm_mul]
    exact mul_le_mul ((le_max_right _ _).trans (le_max_right _ _)) h₃ (norm_nonneg _) hM
  calc ‖m01 A * t₁ + m02 A * t₂ + m12 A * t₃‖
      ≤ ‖m01 A * t₁‖ + ‖m02 A * t₂‖ + ‖m12 A * t₃‖ := norm_add₃_le
    _ ≤ minorMax A * (2 * entryBound G ^ 2) + minorMax A * (2 * entryBound G ^ 2)
        + minorMax A * (2 * entryBound G ^ 2) := by linarith
    _ = 6 * entryBound G ^ 2 * minorMax A := by ring

theorem minorMax_mul_le (A G : Matrix (Fin 3) (Fin 3) F) :
    minorMax (A * G) ≤ 6 * entryBound G ^ 2 * minorMax A := by
  refine max_le ?_ (max_le ?_ ?_)
  · rw [m01_mul]
    exact norm_combination_le A G _ _ _ (norm_twoMinor_le G 0 1 0 1) (norm_twoMinor_le G 0 2 0 1)
      (norm_twoMinor_le G 1 2 0 1)
  · rw [m02_mul]
    exact norm_combination_le A G _ _ _ (norm_twoMinor_le G 0 1 0 2) (norm_twoMinor_le G 0 2 0 2)
      (norm_twoMinor_le G 1 2 0 2)
  · rw [m12_mul]
    exact norm_combination_le A G _ _ _ (norm_twoMinor_le G 0 1 1 2) (norm_twoMinor_le G 0 2 1 2)
      (norm_twoMinor_le G 1 2 1 2)

end Invariants

section Majorant

variable {v}

def maj (σ : Fin 3 → ℝ) (A : Matrix (Fin 3) (Fin 3) F) : ℝ :=
  ‖A.det‖ ^ (σ 0 + 1) * minorMax A ^ (σ 1 - σ 0 - 1) * bottomMax A ^ (σ 2 - σ 1 - 1)

theorem maj_nonneg (σ : Fin 3 → ℝ) (A : Matrix (Fin 3) (Fin 3) F) : 0 ≤ maj σ A :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (minorMax_nonneg A) _))
    (Real.rpow_nonneg (bottomMax_nonneg A) _)

def transConst (σ : Fin 3 → ℝ) (g : GL (Fin 3) F) : ℝ :=
  ‖(g : Matrix (Fin 3) (Fin 3) F).det‖ ^ (σ 0 + 1) *
    (6 * entryBound ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 2) ^ (-(σ 1 - σ 0 - 1)) *
    (3 * entryBound ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ^ (-(σ 2 - σ 1 - 1))

theorem transConst_nonneg (σ : Fin 3 → ℝ) (g : GL (Fin 3) F) : 0 ≤ transConst σ g :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (by positivity) _))
    (Real.rpow_nonneg (by linarith [entryBound_pos ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)]) _)

theorem rpow_le_of_div_le {x y C e : ℝ} (hx : 0 < x) (hC : 0 < C) (h : x ≤ C * y) (he : e ≤ 0) :
    y ^ e ≤ x ^ e * C ^ (-e) := by
  have hxy : x / C ≤ y := by rwa [div_le_iff₀' hC]
  calc y ^ e ≤ (x / C) ^ e := Real.rpow_le_rpow_of_nonpos (div_pos hx hC) hxy he
    _ = x ^ e * C ^ (-e) := by rw [Real.div_rpow hx.le hC.le, Real.rpow_neg hC.le, div_eq_mul_inv]

theorem maj_mul_le (σ : Fin 3 → ℝ) (h01 : σ 1 < σ 0 + 1) (h12 : σ 2 < σ 1 + 1)
    (A : Matrix (Fin 3) (Fin 3) F) (hA : A.det ≠ 0) (g : GL (Fin 3) F) :
    maj σ (A * (g : Matrix (Fin 3) (Fin 3) F)) ≤ transConst σ g * maj σ A := by
  set B : Matrix (Fin 3) (Fin 3) F := A * (g : Matrix (Fin 3) (Fin 3) F) with hB
  set G : Matrix (Fin 3) (Fin 3) F := ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hG
  have hBG : B * G = A := by
    rw [hB, hG, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hE := entryBound_pos G

  have hmin : minorMax A ≤ 6 * entryBound G ^ 2 * minorMax B := by
    rw [← hBG]
    exact minorMax_mul_le B G
  have hbot : bottomMax A ≤ 3 * entryBound G * bottomMax B := by
    rw [← hBG]
    exact bottomMax_mul_le B G
  have e1 : minorMax B ^ (σ 1 - σ 0 - 1) ≤
      minorMax A ^ (σ 1 - σ 0 - 1) * (6 * entryBound G ^ 2) ^ (-(σ 1 - σ 0 - 1)) :=
    rpow_le_of_div_le (minorMax_pos hA) (by positivity) hmin (by linarith)
  have e2 : bottomMax B ^ (σ 2 - σ 1 - 1) ≤
      bottomMax A ^ (σ 2 - σ 1 - 1) * (3 * entryBound G) ^ (-(σ 2 - σ 1 - 1)) :=
    rpow_le_of_div_le (bottomMax_pos hA) (by positivity) hbot (by linarith)
  have e0 : ‖B.det‖ ^ (σ 0 + 1) = ‖A.det‖ ^ (σ 0 + 1) * ‖(g : Matrix (Fin 3) (Fin 3) F).det‖ ^ (σ 0 + 1) := by
    rw [hB, Matrix.det_mul, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  unfold maj transConst
  rw [e0]
  have n0 : 0 ≤ ‖A.det‖ ^ (σ 0 + 1) * ‖(g : Matrix (Fin 3) (Fin 3) F).det‖ ^ (σ 0 + 1) :=
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)
  calc ‖A.det‖ ^ (σ 0 + 1) * ‖(g : Matrix (Fin 3) (Fin 3) F).det‖ ^ (σ 0 + 1) * minorMax B ^ (σ 1 - σ 0 - 1)
        * bottomMax B ^ (σ 2 - σ 1 - 1)
      ≤ ‖A.det‖ ^ (σ 0 + 1) * ‖(g : Matrix (Fin 3) (Fin 3) F).det‖ ^ (σ 0 + 1)
        * (minorMax A ^ (σ 1 - σ 0 - 1) * (6 * entryBound G ^ 2) ^ (-(σ 1 - σ 0 - 1)))
        * (bottomMax A ^ (σ 2 - σ 1 - 1) * (3 * entryBound G) ^ (-(σ 2 - σ 1 - 1))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left e1 n0) e2 (Real.rpow_nonneg (bottomMax_nonneg B) _)
          (mul_nonneg n0 (mul_nonneg (Real.rpow_nonneg (minorMax_nonneg A) _) (Real.rpow_nonneg (by positivity) _)))
    _ = _ := by ring

end Majorant

section AtW0

variable {v}

theorem w0n_coe (x y z : F) :
    ((antidiagonal3 v * upperUnipotent3 x y z : LocalGL3 v) : Matrix (Fin 3) (Fin 3) F) =
      !![0, 0, 1; 0, 1, y; 1, x, z] := by
  rw [Units.val_mul, antidiagonal3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem det_w0n (x y z : F) :
    ((antidiagonal3 v * upperUnipotent3 x y z : LocalGL3 v) : Matrix (Fin 3) (Fin 3) F).det = -1 := by
  rw [w0n_coe]
  simp [Matrix.det_fin_three]

theorem bottomMax_w0n (x y z : F) :
    bottomMax ((antidiagonal3 v * upperUnipotent3 x y z : LocalGL3 v) : Matrix (Fin 3) (Fin 3) F) =
      max 1 (max ‖x‖ ‖z‖) := by
  rw [w0n_coe]
  simp [bottomMax]

theorem minorMax_w0n (x y z : F) :
    minorMax ((antidiagonal3 v * upperUnipotent3 x y z : LocalGL3 v) : Matrix (Fin 3) (Fin 3) F) =
      max 1 (max ‖y‖ ‖z - x * y‖) := by
  rw [w0n_coe]
  simp [minorMax, m01, m02, m12, mul_comm y x]

theorem maj_w0n (σ : Fin 3 → ℝ) (x y z : F) :
    maj σ ((antidiagonal3 v * upperUnipotent3 x y z : LocalGL3 v) : Matrix (Fin 3) (Fin 3) F) =
      (max 1 (max ‖y‖ ‖z - x * y‖)) ^ (σ 1 - σ 0 - 1) * (max 1 (max ‖x‖ ‖z‖)) ^ (σ 2 - σ 1 - 1) := by
  rw [maj, det_w0n, minorMax_w0n, bottomMax_w0n, norm_neg, norm_one, Real.one_rpow, one_mul]

end AtW0

section CellBound

variable {v}

theorem rpow_bookkeeping {D L c : ℝ} (hD : 0 < D) (hL : 0 < L) (hc : 0 < c) (s₀ s₁ s₂ : ℝ) :
    (D / L) ^ s₀ * (L / c) ^ s₁ * c ^ s₂ * (D / L / c) = D ^ (s₀ + 1) * L ^ (s₁ - s₀ - 1) * c ^ (s₂ - s₁ - 1) := by
  rw [Real.div_rpow hD.le hL.le, Real.div_rpow hL.le hc.le, Real.rpow_add hD, Real.rpow_one,
    Real.rpow_sub hL, Real.rpow_sub hL, Real.rpow_one, Real.rpow_sub hc, Real.rpow_sub hc, Real.rpow_one]
  have h1 : D ^ s₀ ≠ 0 := (Real.rpow_pos_of_pos hD _).ne'
  have h2 : L ^ s₀ ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
  have h3 : L ^ s₁ ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
  have h4 : c ^ s₁ ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  have h5 : c ^ s₂ ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  field_simp

theorem norm_cellValue_eq (ν : Fin 3 → (Fˣ →* ℂˣ)) (σ : Fin 3 → ℝ)
    (hσ : ∀ (i : Fin 3) (x : Fˣ), ‖((ν i x : ℂˣ) : ℂ)‖ = ‖(x : F)‖ ^ (σ i))
    {h : LocalGL3 v} (hc : cornerEntry v h ≠ 0) (hL : lowerMinor v h ≠ 0) :
    ‖cellValue v ν h‖ =
      ‖gl3Det v h‖ ^ (σ 0 + 1) * ‖lowerMinor v h‖ ^ (σ 1 - σ 0 - 1) * ‖cornerEntry v h‖ ^ (σ 2 - σ 1 - 1) := by
  have hdet := gl3Det_ne_zero v h
  have hq0 : gl3Det v h / lowerMinor v h ≠ 0 := div_ne_zero hdet hL
  have hq1 : lowerMinor v h / cornerEntry v h ≠ 0 := div_ne_zero hL hc
  have e0 : ‖charExt (ν 0) (gl3Det v h / lowerMinor v h)‖ = (‖gl3Det v h‖ / ‖lowerMinor v h‖) ^ (σ 0) := by
    rw [charExt_of_ne_zero _ hq0, hσ 0, Units.val_mk0, norm_div]
  have e1 : ‖charExt (ν 1) (lowerMinor v h / cornerEntry v h)‖ = (‖lowerMinor v h‖ / ‖cornerEntry v h‖) ^ (σ 1) := by
    rw [charExt_of_ne_zero _ hq1, hσ 1, Units.val_mk0, norm_div]
  have e2 : ‖charExt (ν 2) (cornerEntry v h)‖ = ‖cornerEntry v h‖ ^ (σ 2) := by
    rw [charExt_of_ne_zero _ hc, hσ 2, Units.val_mk0]
  have e3 : ‖(((‖gl3Det v h / lowerMinor v h‖ / ‖cornerEntry v h‖ : ℝ)) : ℂ)‖ =
      ‖gl3Det v h‖ / ‖lowerMinor v h‖ / ‖cornerEntry v h‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_div]
  rw [cellValue, norm_mul, norm_mul, norm_mul, e0, e1, e2, e3]
  exact rpow_bookkeeping (norm_pos_iff.mpr hdet) (norm_pos_iff.mpr hL) (norm_pos_iff.mpr hc) _ _ _

def cellConst (σ : Fin 3 → ℝ) (B R : ℝ) : ℝ :=
  B * ((2 * R ^ 2) ^ (-(σ 1 - σ 0 - 1)) * R ^ (-(σ 2 - σ 1 - 1)))

theorem cellConst_nonneg (σ : Fin 3 → ℝ) {B R : ℝ} (hB : 0 ≤ B) (hR : 1 ≤ R) : 0 ≤ cellConst σ B R :=
  mul_nonneg hB (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by linarith) _))

theorem norm_cellSectionOf_le (ν : Fin 3 → (Fˣ →* ℂˣ)) (σ : Fin 3 → ℝ)
    (hσ : ∀ (i : Fin 3) (x : Fˣ), ‖((ν i x : ℂˣ) : ℂ)‖ = ‖(x : F)‖ ^ (σ i))
    (h01 : σ 1 < σ 0 + 1) (h12 : σ 2 < σ 1 + 1)
    (Φ : (Fin 3 → F) → ℂ) {B R : ℝ} (hB : ∀ r, ‖Φ r‖ ≤ B) (hR : 1 ≤ R)
    (hsupp : ∀ r, Φ r ≠ 0 → ∀ i, ‖r i‖ ≤ R) (h : LocalGL3 v) :
    ‖cellSectionOf v ν Φ h‖ ≤ cellConst σ B R * maj σ (h : Matrix (Fin 3) (Fin 3) F) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hK := cellConst_nonneg σ hB0 hR
  set A : Matrix (Fin 3) (Fin 3) F := (h : Matrix (Fin 3) (Fin 3) F) with hA
  have hAdet : A.det ≠ 0 := gl3Det_ne_zero v h
  by_cases hcell : h ∈ bigCell3 v
  swap
  · rw [cellSectionOf_apply_of_notMem _ _ _ hcell, norm_zero]
    exact mul_nonneg hK (maj_nonneg σ A)
  rw [cellSectionOf_apply_of_mem _ _ _ hcell]
  obtain ⟨hc, hL⟩ := (mem_bigCell3_iff v h).mp hcell
  by_cases hΦ0 : Φ (cellRatio v h) = 0
  · rw [hΦ0, mul_zero, norm_zero]
    exact mul_nonneg hK (maj_nonneg σ A)

  have nc : 0 < ‖cornerEntry v h‖ := norm_pos_iff.mpr hc
  have nL : 0 < ‖lowerMinor v h‖ := norm_pos_iff.mpr hL
  have hcA : cornerEntry v h = A 2 0 := rfl
  have hLA : lowerMinor v h = m01 A := rfl
  have hOA : outerMinor v h = m02 A := rfl
  have hR2 : R ≤ 2 * R ^ 2 := by nlinarith
  have hR2' : 1 ≤ 2 * R ^ 2 := hR.trans hR2

  have hr := hsupp _ hΦ0
  have hr0 : ‖A 2 1‖ ≤ R * ‖cornerEntry v h‖ := by
    have := hr 0
    simp only [cellRatio, Matrix.cons_val_zero, norm_div] at this
    rwa [div_le_iff₀ nc] at this
  have hr1 : ‖A 2 2‖ ≤ R * ‖cornerEntry v h‖ := by
    have := hr 1
    simp only [cellRatio, Matrix.cons_val_one, Matrix.cons_val_zero, norm_div] at this
    rwa [div_le_iff₀ nc] at this
  have hr2 : ‖m02 A‖ ≤ R * ‖lowerMinor v h‖ := by
    have := hr 2
    simp only [cellRatio, Matrix.cons_val, norm_div] at this
    rwa [div_le_iff₀ nL] at this

  have hbot : bottomMax A ≤ R * ‖cornerEntry v h‖ := by
    refine max_le ?_ (max_le hr0 hr1)
    rw [← hcA]
    exact le_mul_of_one_le_left nc.le hR
  have hmin : minorMax A ≤ (2 * R ^ 2) * ‖lowerMinor v h‖ := by
    refine max_le ?_ (max_le ?_ ?_)
    · rw [← hLA]
      exact le_mul_of_one_le_left nL.le hR2'
    · exact hr2.trans (mul_le_mul_of_nonneg_right hR2 nL.le)
    ·
      have hsyz : cornerEntry v h * m12 A = A 2 1 * m02 A - A 2 2 * m01 A := by
        rw [hcA]
        simp only [m12, m02, m01]
        ring
      have hnorm : ‖cornerEntry v h‖ * ‖m12 A‖ ≤ ‖cornerEntry v h‖ * ((2 * R ^ 2) * ‖lowerMinor v h‖) := by
        rw [← norm_mul, hsyz]
        calc ‖A 2 1 * m02 A - A 2 2 * m01 A‖
            ≤ ‖A 2 1 * m02 A‖ + ‖A 2 2 * m01 A‖ := norm_sub_le _ _
          _ ≤ R * ‖cornerEntry v h‖ * (R * ‖lowerMinor v h‖) + R * ‖cornerEntry v h‖ * ‖lowerMinor v h‖ := by
              rw [norm_mul, norm_mul, ← hLA]
              exact add_le_add (mul_le_mul hr0 hr2 (norm_nonneg _) (by positivity))
                (mul_le_mul_of_nonneg_right hr1 (norm_nonneg _))
          _ = ‖cornerEntry v h‖ * ‖lowerMinor v h‖ * (R ^ 2 + R) := by ring
          _ ≤ ‖cornerEntry v h‖ * ‖lowerMinor v h‖ * (2 * R ^ 2) := by
              apply mul_le_mul_of_nonneg_left _ (mul_nonneg nc.le nL.le)
              nlinarith
          _ = ‖cornerEntry v h‖ * ((2 * R ^ 2) * ‖lowerMinor v h‖) := by ring
      exact le_of_mul_le_mul_left hnorm nc

  have hval := norm_cellValue_eq ν σ hσ hc hL
  have e1 : ‖lowerMinor v h‖ ^ (σ 1 - σ 0 - 1) ≤
      minorMax A ^ (σ 1 - σ 0 - 1) * (2 * R ^ 2) ^ (-(σ 1 - σ 0 - 1)) :=
    rpow_le_of_div_le (minorMax_pos hAdet) (by positivity) hmin (by linarith)
  have e2 : ‖cornerEntry v h‖ ^ (σ 2 - σ 1 - 1) ≤
      bottomMax A ^ (σ 2 - σ 1 - 1) * R ^ (-(σ 2 - σ 1 - 1)) :=
    rpow_le_of_div_le (bottomMax_pos hAdet) (by linarith) hbot (by linarith)
  have hD : ‖gl3Det v h‖ ^ (σ 0 + 1) = ‖A.det‖ ^ (σ 0 + 1) := rfl
  have n0 : 0 ≤ ‖A.det‖ ^ (σ 0 + 1) := Real.rpow_nonneg (norm_nonneg _) _
  rw [norm_mul, hval, hD]
  calc ‖A.det‖ ^ (σ 0 + 1) * ‖lowerMinor v h‖ ^ (σ 1 - σ 0 - 1) * ‖cornerEntry v h‖ ^ (σ 2 - σ 1 - 1)
        * ‖Φ (cellRatio v h)‖
      ≤ ‖A.det‖ ^ (σ 0 + 1) * (minorMax A ^ (σ 1 - σ 0 - 1) * (2 * R ^ 2) ^ (-(σ 1 - σ 0 - 1)))
        * (bottomMax A ^ (σ 2 - σ 1 - 1) * R ^ (-(σ 2 - σ 1 - 1))) * B := by
        refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left e1 n0) e2
          (Real.rpow_nonneg (norm_nonneg _) _) (mul_nonneg n0 (mul_nonneg (Real.rpow_nonneg (minorMax_nonneg A) _)
            (Real.rpow_nonneg (by positivity) _)))) (hB _) (norm_nonneg _) ?_
        exact mul_nonneg (mul_nonneg n0 (mul_nonneg (Real.rpow_nonneg (minorMax_nonneg A) _)
          (Real.rpow_nonneg (by positivity) _))) (mul_nonneg (Real.rpow_nonneg (bottomMax_nonneg A) _)
            (Real.rpow_nonneg (by linarith) _))
    _ = cellConst σ B R * maj σ A := by
        unfold cellConst maj
        ring

end CellBound

section Main

theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ v
    (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  letI := localBorel ℚ v
  haveI : BorelSpace F := ⟨rfl⟩
  have hq : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 := by
    have h : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)
  have hc : ((Ideal.absNorm v.asIdeal : ℝ≥0) ^
      (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2)) ≠ 0 :=
    (NNReal.rpow_pos (pos_iff_ne_zero.mpr hq)).ne'
  show ((((Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2))
    • Measure.addHaarMeasure (integersPositiveCompacts ℚ v) : Measure F)).IsAddHaarMeasure
  rw [ENNReal.smul_def]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc) ENNReal.coe_ne_top

theorem continuous_upperUnipotent3_prod :
    Continuous fun p : F × F × F => (upperUnipotent3 p.1 p.2.1 p.2.2 : LocalGL3 v) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun p : F × F × F => ((upperUnipotent3 p.1 p.2.1 p.2.2 : LocalGL3 v) : Matrix (Fin 3) (Fin 3) F)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop
  · change Continuous fun p : F × F × F => (upperUnipotent3 p.1 p.2.1 p.2.2 : LocalGL3 v).inv
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop

theorem main
    (ν : Fin 3 → (Fˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (σ : Fin 3 → ℝ)
    (hσ : ∀ (i : Fin 3) (x : Fˣ), ‖((ν i x : ℂˣ) : ℂ)‖ = ‖(x : F)‖ ^ (σ i))
    (h01 : σ 1 < σ 0) (h12 : σ 2 < σ 1)
    (Φ : (Fin 3 → F) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (g : LocalGL3 v) :
    letI := localBorel ℚ v
    Integrable (fun p : F × F × F =>
      cellSectionOf v ν Φ (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * g)) (jacquetHaar3 v) := by
  letI : MeasurableSpace F := localBorel ℚ v
  haveI : BorelSpace F := ⟨rfl⟩
  set μ : Measure F := selfDualHaarAt ℚ v with hμdef
  haveI : μ.IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt v
  have hJ : jacquetHaar3 v = μ.prod (μ.prod μ) := rfl

  set a : ℝ := σ 0 - σ 1 with ha_def
  set b : ℝ := σ 1 - σ 2 with hb_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have hb : 0 < b := by rw [hb_def]; linarith
  have h01' : σ 1 < σ 0 + 1 := by linarith
  have h12' : σ 2 < σ 1 + 1 := by linarith

  obtain ⟨B, hB⟩ := hΦ.1.continuous.bounded_above_of_compact_support hΦ.2
  obtain ⟨R, hR1, hR⟩ : ∃ R : ℝ, 1 ≤ R ∧ ∀ r, Φ r ≠ 0 → ∀ i, ‖r i‖ ≤ R := by
    obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hΦ.2.isCompact.isBounded
    refine ⟨max R₀ 1, le_max_right _ _, fun r hr i => ?_⟩
    have hmem : r ∈ tsupport Φ := subset_tsupport Φ (Function.mem_support.mpr hr)
    have h := hR₀ hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact (norm_le_pi_norm r i).trans (h.trans (le_max_left _ _))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)

  obtain ⟨Λ₀, Λ₁, -, -, hcellmem, -⟩ :=
    exists_isWhittakerFunctional3_psiLocal_and_inv_eq_jacquetValue_and_eq_sum v ν hν
  obtain ⟨hmem, -⟩ := hcellmem Φ hΦ
  have hlc : IsLocallyConstant (cellSectionOf v ν Φ) := isLocallyConstant_of_mem_principalSeries3 hmem
  have hφ : Continuous fun p : F × F × F => antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * g :=
    (continuous_const.mul (continuous_upperUnipotent3_prod v)).mul continuous_const
  have hsm : AEStronglyMeasurable (fun p : F × F × F =>
      cellSectionOf v ν Φ (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * g)) (jacquetHaar3 v) :=
    (hlc.comp_continuous hφ).continuous.aestronglyMeasurable
  refine ⟨hsm, ?_⟩

  set K : ℝ := cellConst σ B R * transConst σ g with hK_def
  have hK0 : 0 ≤ K := mul_nonneg (cellConst_nonneg σ hB0 hR1) (transConst_nonneg σ g)
  have hpt : ∀ p : F × F × F,
      ENNReal.ofReal ‖cellSectionOf v ν Φ (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * g)‖ ≤
        ENNReal.ofReal K * ker v a b p := by
    rintro ⟨x, y, z⟩
    set w : LocalGL3 v := antidiagonal3 v * upperUnipotent3 x y z with hw
    have hwdet : (w : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
      rw [hw, det_w0n]
      exact neg_ne_zero.mpr one_ne_zero
    have h1 : ‖cellSectionOf v ν Φ (w * g)‖ ≤ cellConst σ B R * maj σ ((w * g : LocalGL3 v) : Matrix (Fin 3) (Fin 3) F) :=
      norm_cellSectionOf_le ν σ hσ h01' h12' Φ hB hR1 hR (w * g)
    have h2 : maj σ ((w * g : LocalGL3 v) : Matrix (Fin 3) (Fin 3) F) ≤
        transConst σ g * maj σ (w : Matrix (Fin 3) (Fin 3) F) := by
      rw [Units.val_mul]
      exact maj_mul_le σ h01' h12' _ hwdet g
    have h3 : maj σ (w : Matrix (Fin 3) (Fin 3) F) = sh b (max ‖x‖ ‖z‖) * sh a (max ‖y‖ ‖z - x * y‖) := by
      rw [hw, maj_w0n, sh, sh, mul_comm]
      congr 2 <;> simp only [ha_def, hb_def] <;> ring
    have h4 : ‖cellSectionOf v ν Φ (w * g)‖ ≤ K * (sh b (max ‖x‖ ‖z‖) * sh a (max ‖y‖ ‖z - x * y‖)) := by
      have h := h1.trans (mul_le_mul_of_nonneg_left h2 (cellConst_nonneg σ hB0 hR1))
      rw [h3] at h
      calc _ ≤ _ := h
        _ = K * (sh b (max ‖x‖ ‖z‖) * sh a (max ‖y‖ ‖z - x * y‖)) := by rw [hK_def]; ring
    show ENNReal.ofReal ‖cellSectionOf v ν Φ (w * g)‖ ≤ ENNReal.ofReal K * (kerA v b x z * kerB v a x y z)
    rw [kerA, kerB, ← ENNReal.ofReal_mul (sh_nonneg _ _), ← ENNReal.ofReal_mul hK0]
    exact ENNReal.ofReal_le_ofReal h4
  rw [hasFiniteIntegral_iff_norm]
  calc ∫⁻ p, ENNReal.ofReal ‖cellSectionOf v ν Φ (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * g)‖
        ∂(jacquetHaar3 v)
      ≤ ∫⁻ p, ENNReal.ofReal K * ker v a b p ∂(μ.prod (μ.prod μ)) := by
        rw [hJ]
        exact lintegral_mono hpt
    _ = ENNReal.ofReal K * ∫⁻ p, ker v a b p ∂(μ.prod (μ.prod μ)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_ker_lt_top v μ ha hb)

end Main

end LTGKRankTwo

end

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (σ : Fin 3 → ℝ)
    (hσ : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖((ν i x : ℂˣ) : ℂ)‖ = ‖(x : v.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0) (h12 : σ 2 < σ 1)
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (g : LocalGL3 v) :
    letI := localBorel ℚ v
    Integrable (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      cellSectionOf v ν Φ (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * g)) (jacquetHaar3 v) :=
  LTGKRankTwo.main v ν hν σ hσ h01 h12 Φ hΦ g

end S_LanglandsTunnell_CubicInduction_integrable_cellSectionOf_antidiagonal3_mul_upperUnipotent3_mul_of_norm_eq_rpow_of_lt
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_integrable_cellSectionOf_antidiagonal3_mul_upperUnipotent3_mul_of_norm_eq_rpow_of_lt (solution)
