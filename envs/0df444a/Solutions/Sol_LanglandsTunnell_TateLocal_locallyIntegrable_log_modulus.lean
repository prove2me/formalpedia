-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.locallyIntegrable_log_modulus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b6c93bf5-cf6c-5eec-a5c4-c7d913472d43

import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_Completion_Finite
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_locallyIntegrable_log_modulus
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField IsDedekindDomain LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_locallyIntegrable_log_modulus.LanglandsTunnell.TateLocal Set Filter"
open scoped NNReal ENNReal Pointwise Topology

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.modulus TateLocal.modulus_adicCompletion_eq_nnnorm"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "modulus modulus_of_ne_zero modulus_adicCompletion_eq_nnnorm"
namespace LogLoc
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem exists_norm_pos_lt_one : ∃ π : v.adicCompletion K, 0 < ‖π‖ ∧ ‖π‖ < 1 := by
  obtain ⟨x, hxv, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  refine ⟨NumberField.FinitePlace.embedding v (algebraMap (𝓞 K) K x), ?_, ?_⟩
  · rw [norm_pos_iff]
    intro h
    apply hx0
    have h1 : (algebraMap (𝓞 K) K x) = 0 := by
      rwa [map_eq_zero] at h
    exact (FaithfulSMul.algebraMap_eq_zero_iff (𝓞 K) K).mp h1
  · exact (NumberField.FinitePlace.norm_lt_one_iff_mem K v x).mpr hxv

section Measure

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

theorem measure_smul_set {c : v.adicCompletion K} (hc : c ≠ 0) (S : Set (v.adicCompletion K)) :
    μ (c • S) = (‖c‖₊ : ℝ≥0∞) * μ S := by
  have h := distribHaarChar_mul μ (Units.mk0 c hc) S
  rw [show ((Units.mk0 c hc) • S : Set (v.adicCompletion K)) = c • S from rfl] at h
  rw [← h, ← modulus_of_ne_zero hc, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem closedBall_zero_one_subset_integers :
    Metric.closedBall (0 : v.adicCompletion K) 1 ⊆ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, NumberField.FinitePlace.norm_def] at hx
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
    ← (WithZeroMulInt.toNNReal_strictMono (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).le_iff_le,
    map_one]
  exact_mod_cast hx

theorem measure_closedBall_one_lt_top : μ (Metric.closedBall (0 : v.adicCompletion K) 1) < ∞ :=
  lt_of_le_of_lt (measure_mono (closedBall_zero_one_subset_integers v))
    (NumberField.isCompactAdicCompletionIntegers K v).measure_lt_top

theorem measure_closedBall_pow {π : v.adicCompletion K} (hπ : π ≠ 0) (n : ℕ) :
    μ (Metric.closedBall (0 : v.adicCompletion K) (‖π‖ ^ n)) =
      (‖π‖₊ : ℝ≥0∞) ^ n * μ (Metric.closedBall (0 : v.adicCompletion K) 1) := by
  have h := smul_closedBall' (pow_ne_zero n hπ) (0 : v.adicCompletion K) 1
  rw [smul_zero, norm_pow, mul_one] at h
  rw [← h, measure_smul_set v μ (pow_ne_zero n hπ), nnnorm_pow, ENNReal.coe_pow]

theorem integrableOn_norm_rpow_sub_one {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : v.adicCompletion K => ‖x‖ ^ (a - 1))
      {x : v.adicCompletion K | 0 < ‖x‖ ∧ ‖x‖ ≤ 1} μ := by
  obtain ⟨π, hπ0, hπ1⟩ := exists_norm_pos_lt_one v
  have hπne : π ≠ 0 := norm_pos_iff.mp hπ0
  set q : ℝ := ‖π‖ with hq

  set A : ℕ → Set (v.adicCompletion K) := fun n => {x | q ^ (n + 1) < ‖x‖ ∧ ‖x‖ ≤ q ^ n} with hA
  have hcover : {x : v.adicCompletion K | 0 < ‖x‖ ∧ ‖x‖ ≤ 1} ⊆ ⋃ n, A n := by
    intro x hx
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near_of_lt_one hx.1 hx.2 hπ0 hπ1
    exact Set.mem_iUnion.mpr ⟨n, hn1, hn2⟩
  refine IntegrableOn.mono_set ?_ hcover
  have hmeasA : ∀ n, MeasurableSet (A n) := fun n =>
    (measurableSet_lt measurable_const measurable_norm).inter (measurableSet_le measurable_norm measurable_const)
  have hBfin := measure_closedBall_one_lt_top v μ
  have hB : ∀ n : ℕ, μ (A n) ≤ (‖π‖₊ : ℝ≥0∞) ^ n * μ (Metric.closedBall (0 : v.adicCompletion K) 1) := by
    intro n
    rw [← measure_closedBall_pow v μ hπne n]
    exact measure_mono fun x hx => by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hx.2
  have hAfin : ∀ n, μ (A n) < ∞ := fun n =>
    (hB n).trans_lt (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hBfin)
  have hmeas : Measurable fun x : v.adicCompletion K => ‖x‖ ^ (a - 1) := measurable_norm.pow_const _

  have hbound : ∀ n, ∀ x ∈ A n, ‖(‖x‖ ^ (a - 1) : ℝ)‖ ≤ (q ^ n) ^ a * (q ^ (n + 1))⁻¹ := by
    intro n x hx
    have hx0 : 0 < ‖x‖ := lt_trans (pow_pos hπ0 _) hx.1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), Real.rpow_sub_one hx0.ne',
      div_eq_mul_inv]
    exact mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) hx.2 ha.le) (inv_anti₀ (pow_pos hπ0 _) hx.1.le)
      (inv_nonneg.mpr hx0.le) (Real.rpow_nonneg (pow_nonneg hπ0.le _) _)
  have hqpow : ∀ n : ℕ, (q ^ n) ^ a = (q ^ a) ^ n := fun n => by
    rw [← Real.rpow_natCast q n, ← Real.rpow_mul hπ0.le, mul_comm, Real.rpow_mul hπ0.le, Real.rpow_natCast]
  apply integrableOn_iUnion_of_summable_integral_norm
  · intro n
    exact Measure.integrableOn_of_bounded (hAfin n).ne hmeas.aestronglyMeasurable
      ((ae_restrict_mem (hmeasA n)).mono fun x hx => hbound n x hx)
  · have hqa : q ^ a < 1 := Real.rpow_lt_one hπ0.le hπ1 ha
    have hqa0 : 0 ≤ q ^ a := Real.rpow_nonneg hπ0.le _
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one hqa0 hqa).mul_right
        (q⁻¹ * μ.real (Metric.closedBall (0 : v.adicCompletion K) 1)))

    have h1 := norm_setIntegral_le_of_norm_le_const (hAfin n) (fun x hx => by
      rw [norm_norm]; exact hbound n x hx) (f := fun x : v.adicCompletion K => ‖(‖x‖ ^ (a - 1) : ℝ)‖) (μ := μ)
    have h2 : μ.real (A n) ≤ q ^ n * μ.real (Metric.closedBall (0 : v.adicCompletion K) 1) := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hBfin.ne) (hB n)
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm] at this
      exact this
    calc ∫ x in A n, ‖(‖x‖ ^ (a - 1) : ℝ)‖ ∂μ
        ≤ ‖∫ x in A n, ‖(‖x‖ ^ (a - 1) : ℝ)‖ ∂μ‖ := Real.le_norm_self _
      _ ≤ (q ^ n) ^ a * (q ^ (n + 1))⁻¹ * μ.real (A n) := h1
      _ ≤ (q ^ n) ^ a * (q ^ (n + 1))⁻¹ * (q ^ n * μ.real (Metric.closedBall (0 : v.adicCompletion K) 1)) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (Real.rpow_nonneg (pow_nonneg hπ0.le _) _)
            (inv_nonneg.mpr (pow_nonneg hπ0.le _)))
      _ = (q ^ a) ^ n * (q⁻¹ * μ.real (Metric.closedBall (0 : v.adicCompletion K) 1)) := by
          rw [hqpow, pow_succ, mul_inv]
          field_simp

theorem integrableOn_norm_rpow_mul_inv {a : ℝ} (ha : 0 < a) {S : Set (v.adicCompletion K)}
    (hS : IsCompact S) :
    IntegrableOn (fun x : v.adicCompletion K => ‖x‖ ^ a * ‖x‖⁻¹) S μ := by
  obtain ⟨R, hR⟩ := hS.isBounded.exists_norm_le
  have hmeas : Measurable fun x : v.adicCompletion K => ‖x‖ ^ a * ‖x‖⁻¹ :=
    (measurable_norm.pow_const _).mul measurable_norm.inv

  have h0 : IntegrableOn (fun x : v.adicCompletion K => ‖x‖ ^ a * ‖x‖⁻¹) {0} μ :=
    integrableOn_singleton (hx := isCompact_singleton.measure_lt_top)
  have h1 : IntegrableOn (fun x : v.adicCompletion K => ‖x‖ ^ a * ‖x‖⁻¹)
      {x : v.adicCompletion K | 0 < ‖x‖ ∧ ‖x‖ ≤ 1} μ := by
    refine (integrableOn_norm_rpow_sub_one v μ ha).congr_fun (fun x hx => ?_)
      ((measurableSet_lt measurable_const measurable_norm).inter
        (measurableSet_le measurable_norm measurable_const))
    beta_reduce
    rw [Real.rpow_sub_one hx.1.ne', div_eq_mul_inv]
  have h2 : IntegrableOn (fun x : v.adicCompletion K => ‖x‖ ^ a * ‖x‖⁻¹)
      (S ∩ {x : v.adicCompletion K | 1 ≤ ‖x‖}) μ := by
    refine Measure.integrableOn_of_bounded (M := (max R 1) ^ a)
      (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hS.measure_lt_top).ne hmeas.aestronglyMeasurable
      ((ae_restrict_mem (hS.measurableSet.inter (measurableSet_le measurable_const measurable_norm))).mono
        fun x hx => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (inv_nonneg.mpr (norm_nonneg _)))]
    calc ‖x‖ ^ a * ‖x‖⁻¹ ≤ (max R 1) ^ a * 1 :=
          mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) ((hR x hx.1).trans (le_max_left _ _)) ha.le)
            (inv_le_one_of_one_le₀ hx.2) (inv_nonneg.mpr (norm_nonneg _))
            (Real.rpow_nonneg (le_trans zero_le_one (le_max_right _ _)) _)
      _ = (max R 1) ^ a := mul_one _
  refine ((h0.union h1).union h2).mono_set fun x hx => ?_
  by_cases hx0 : x = 0
  · exact Or.inl (Or.inl hx0)
  · by_cases hx1 : ‖x‖ ≤ 1
    · exact Or.inl (Or.inr ⟨norm_pos_iff.mpr hx0, hx1⟩)
    · exact Or.inr ⟨hx, le_of_not_ge hx1⟩

theorem integrableOn_log_norm {S : Set (v.adicCompletion K)} (hS : IsCompact S) :
    IntegrableOn (fun x : v.adicCompletion K => Real.log ‖x‖) S μ := by
  obtain ⟨R, hR⟩ := hS.isBounded.exists_norm_le
  have hmeas : Measurable fun x : v.adicCompletion K => Real.log ‖x‖ := Real.measurable_log.comp measurable_norm
  have h0 : IntegrableOn (fun x : v.adicCompletion K => Real.log ‖x‖) {0} μ :=
    integrableOn_singleton (hx := isCompact_singleton.measure_lt_top)
  have hmA : MeasurableSet {x : v.adicCompletion K | 0 < ‖x‖ ∧ ‖x‖ ≤ 1} :=
    (measurableSet_lt measurable_const measurable_norm).inter (measurableSet_le measurable_norm measurable_const)
  have h1 : IntegrableOn (fun x : v.adicCompletion K => Real.log ‖x‖)
      {x : v.adicCompletion K | 0 < ‖x‖ ∧ ‖x‖ ≤ 1} μ := by
    have hg : IntegrableOn (fun x : v.adicCompletion K => 2 * ‖x‖ ^ ((1 / 2 : ℝ) - 1))
        {x : v.adicCompletion K | 0 < ‖x‖ ∧ ‖x‖ ≤ 1} μ :=
      (integrableOn_norm_rpow_sub_one v μ (by norm_num : (0 : ℝ) < 1 / 2)).const_mul 2
    refine Integrable.mono' hg hmeas.aestronglyMeasurable ((ae_restrict_mem hmA).mono fun x hx => ?_)
    have hxpos : 0 < ‖x‖ := hx.1
    have hq0 : 0 < ‖x‖ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hxpos _
    have hB : |Real.log ‖x‖ * ‖x‖ ^ (1 / 2 : ℝ)| < 1 / (1 / 2 : ℝ) :=
      Real.abs_log_mul_self_rpow_lt ‖x‖ (1 / 2) hxpos hx.2 (by norm_num)
    rw [abs_mul, abs_of_pos hq0, one_div_one_div] at hB
    have hlt : |Real.log ‖x‖| < 2 / ‖x‖ ^ (1 / 2 : ℝ) := (lt_div_iff₀ hq0).mpr hB
    have hpow : ‖x‖ ^ ((1 / 2 : ℝ) - 1) = (‖x‖ ^ (1 / 2 : ℝ))⁻¹ := by
      rw [show ((1 / 2 : ℝ) - 1) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg hxpos.le]
    rw [Real.norm_eq_abs, hpow, ← div_eq_mul_inv]
    exact hlt.le
  have h2 : IntegrableOn (fun x : v.adicCompletion K => Real.log ‖x‖)
      (S ∩ {x : v.adicCompletion K | 1 ≤ ‖x‖}) μ := by
    refine Measure.integrableOn_of_bounded (M := Real.log (max R 1))
      (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hS.measure_lt_top).ne hmeas.aestronglyMeasurable
      ((ae_restrict_mem (hS.measurableSet.inter (measurableSet_le measurable_const measurable_norm))).mono
        fun x hx => ?_)
    have h1x : 1 ≤ ‖x‖ := hx.2
    have hxpos : 0 < ‖x‖ := lt_of_lt_of_le one_pos h1x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg h1x)]
    exact Real.log_le_log hxpos ((hR x hx.1).trans (le_max_left _ _))
  refine ((h0.union h1).union h2).mono_set fun x hx => ?_
  by_cases hx0 : x = 0
  · exact Or.inl (Or.inl hx0)
  · by_cases hx1 : ‖x‖ ≤ 1
    · exact Or.inl (Or.inr ⟨norm_pos_iff.mpr hx0, hx1⟩)
    · exact Or.inr ⟨hx, le_of_not_ge hx1⟩

theorem locallyIntegrable_log_modulus :
    LocallyIntegrable (fun y : v.adicCompletion K => Real.log (modulus y : ℝ)) μ := by
  have hfun : (fun y : v.adicCompletion K => Real.log (modulus y : ℝ)) = fun y => Real.log ‖y‖ := by
    funext y
    rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, coe_nnnorm]
  rw [hfun]
  intro x
  obtain ⟨k, hk, hkx⟩ := exists_compact_mem_nhds x
  exact ⟨k, hkx, integrableOn_log_norm v μ hk⟩

end Measure

end LanglandsTunnell.TateLocal.LogLoc

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] :
    LocallyIntegrable (fun y : v.adicCompletion K => Real.log (LanglandsTunnell.TateLocal.modulus y : ℝ)) μ :=
  LanglandsTunnell.TateLocal.LogLoc.locallyIntegrable_log_modulus v μ

end

end S_LanglandsTunnell_TateLocal_locallyIntegrable_log_modulus
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_locallyIntegrable_log_modulus (solution)
