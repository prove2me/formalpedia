-- Prove2me | solution 1 for NumberField.AdicCompletion.lintegral_inv_max_one_norm_sq_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c0657878-bbf1-543a-881a-a3a74bfdcb3b

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_NumberField_AdicCompletion_map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdicCompletion_lintegral_inv_max_one_norm_sq_lt_top
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal

set_option maxHeartbeats 6400000 in
theorem solution
    (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))
    [MeasurableSpace (w.adicCompletion L)] [BorelSpace (w.adicCompletion L)]
    (ν : Measure (w.adicCompletion L)) [ν.IsAddHaarMeasure] :
    ∫⁻ y : w.adicCompletion L, (ENNReal.ofReal ((max 1 ‖y‖) ^ 2))⁻¹ ∂ν < ⊤ := by
  classical

  obtain ⟨π₀, hπ₀⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer L w
  set π : w.adicCompletion L := (π₀ : w.adicCompletion L) with hπ
  have hvπ : Valued.v π = WithZero.exp (-1 : ℤ) := by
    rw [hπ, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ₀]
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hvπ
    exact WithZero.exp_ne_zero hvπ.symm
  have hπ1 : ‖π‖ < 1 := by
    rw [NumberField.FinitePlace.norm_def, hvπ]
    have hlt : WithZero.exp (-1 : ℤ) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    have := (WithZeroMulInt.toNNReal_lt_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal w)).2 hlt
    exact_mod_cast this
  set r : ℝ := ‖π‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 hπ0
  have hr1 : r < 1 := hπ1
  have hrinv : 1 < r⁻¹ := one_lt_inv_iff₀.2 ⟨hr0, hr1⟩

  set B : Set (w.adicCompletion L) := Metric.closedBall 0 1 with hB
  have hBc : IsCompact B := isCompact_closedBall 0 1
  have hBfin : ν B < ⊤ := hBc.measure_lt_top

  have hscale : ∀ k : ℕ, ν (Metric.closedBall (0 : w.adicCompletion L) (r⁻¹ ^ (k + 1))) =
      ENNReal.ofReal (r⁻¹ ^ (k + 1)) * ν B := by
    intro k
    let T : w.adicCompletion L →ₗ[w.adicCompletion L] w.adicCompletion L := (π ^ (k + 1)) • LinearMap.id
    have hTapp : ∀ y, T y = π ^ (k + 1) * y := fun y => rfl
    have hdet : LinearMap.det T = π ^ (k + 1) := by
      simp only [T, LinearMap.det_smul, Module.finrank_self, pow_one, LinearMap.det_id, mul_one]
    have hT := NumberField.AdicCompletion.map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure L w
      (w.adicCompletion L) ν T (by rw [hdet]; exact pow_ne_zero _ hπ0)
    have hmeasT : Measurable T := (continuous_const.mul continuous_id : Continuous fun y : w.adicCompletion L => π ^ (k + 1) * y).measurable
    have hpre : T ⁻¹' B = Metric.closedBall (0 : w.adicCompletion L) (r⁻¹ ^ (k + 1)) := by
      ext y
      simp only [Set.mem_preimage, hB, Metric.mem_closedBall, dist_zero_right, hTapp, norm_mul, norm_pow, ← hr]
      rw [inv_pow, ← one_div, le_div_iff₀ (pow_pos hr0 _), mul_comm]
    calc ν (Metric.closedBall (0 : w.adicCompletion L) (r⁻¹ ^ (k + 1))) = ν (T ⁻¹' B) := by rw [hpre]
      _ = Measure.map T ν B := (Measure.map_apply hmeasT measurableSet_closedBall).symm
      _ = (ENNReal.ofReal ‖LinearMap.det T‖⁻¹ • ν) B := by rw [hT]
      _ = ENNReal.ofReal (r⁻¹ ^ (k + 1)) * ν B := by
          rw [Measure.smul_apply, smul_eq_mul, hdet, norm_pow, ← hr, inv_pow]

  set g : w.adicCompletion L → ℝ≥0∞ := fun y => B.indicator 1 y +
      ∑' k : ℕ, ENNReal.ofReal (r ^ (2 * k)) *
        (Metric.closedBall (0 : w.adicCompletion L) (r⁻¹ ^ (k + 1))).indicator 1 y with hg
  have hfg : ∀ y : w.adicCompletion L, (ENNReal.ofReal ((max 1 ‖y‖) ^ 2))⁻¹ ≤ g y := by
    intro y
    by_cases hy : ‖y‖ ≤ 1
    · have hm : max 1 ‖y‖ = 1 := max_eq_left hy
      rw [hm, one_pow, ENNReal.ofReal_one, inv_one]
      have hyB : y ∈ B := by rw [hB, Metric.mem_closedBall, dist_zero_right]; exact hy
      calc (1 : ℝ≥0∞) = B.indicator 1 y := by rw [Set.indicator_of_mem hyB, Pi.one_apply]
        _ ≤ g y := le_self_add
    · push Not at hy
      obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hy.le hrinv
      have hm : max 1 ‖y‖ = ‖y‖ := max_eq_right hy.le
      rw [hm]
      have hypos : 0 < ‖y‖ ^ 2 := by positivity
      have h1 : (ENNReal.ofReal (‖y‖ ^ 2))⁻¹ ≤ ENNReal.ofReal (r ^ (2 * n)) := by
        rw [← ENNReal.ofReal_inv_of_pos hypos]
        apply ENNReal.ofReal_le_ofReal
        rw [inv_le_comm₀ hypos (by positivity)]
        calc (r ^ (2 * n))⁻¹ = (r⁻¹ ^ n) ^ 2 := by rw [← inv_pow, mul_comm, pow_mul]
          _ ≤ ‖y‖ ^ 2 := by gcongr
      have hyk : y ∈ Metric.closedBall (0 : w.adicCompletion L) (r⁻¹ ^ (n + 1)) := by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hn2.le
      have h2 : ENNReal.ofReal (r ^ (2 * n)) ≤ g y := by
        calc ENNReal.ofReal (r ^ (2 * n))
            = ENNReal.ofReal (r ^ (2 * n)) *
                (Metric.closedBall (0 : w.adicCompletion L) (r⁻¹ ^ (n + 1))).indicator 1 y := by
              rw [Set.indicator_of_mem hyk, Pi.one_apply, mul_one]
          _ ≤ ∑' k : ℕ, ENNReal.ofReal (r ^ (2 * k)) *
                (Metric.closedBall (0 : w.adicCompletion L) (r⁻¹ ^ (k + 1))).indicator 1 y :=
              ENNReal.le_tsum n
          _ ≤ g y := le_add_self
      exact h1.trans h2

  have hmeasB : MeasurableSet B := measurableSet_closedBall
  have hgint : ∫⁻ y, g y ∂ν = ν B + ∑' k : ℕ, ENNReal.ofReal (r ^ (2 * k)) *
      ν (Metric.closedBall (0 : w.adicCompletion L) (r⁻¹ ^ (k + 1))) := by
    rw [hg]
    rw [lintegral_add_left ((measurable_one.indicator hmeasB))]
    rw [lintegral_indicator_one hmeasB]
    congr 1
    rw [lintegral_tsum (fun k => ((measurable_one.indicator measurableSet_closedBall).const_mul _).aemeasurable)]
    congr 1; funext k
    rw [lintegral_const_mul _ (measurable_one.indicator measurableSet_closedBall), lintegral_indicator_one measurableSet_closedBall]
  have hsum : ∑' k : ℕ, ENNReal.ofReal (r ^ (2 * k)) * ν (Metric.closedBall (0 : w.adicCompletion L) (r⁻¹ ^ (k + 1))) =
      ENNReal.ofReal r⁻¹ * ν B * ∑' k : ℕ, ENNReal.ofReal r ^ k := by
    rw [← ENNReal.tsum_mul_left]
    congr 1; funext k
    rw [hscale k, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow hr0.le]
    have : r ^ (2 * k) * r⁻¹ ^ (k + 1) = r⁻¹ * r ^ k := by
      rw [inv_pow]
      (try field_simp); (try ring)
    rw [this, ENNReal.ofReal_mul (by positivity)]
    ring
  calc ∫⁻ y : w.adicCompletion L, (ENNReal.ofReal ((max 1 ‖y‖) ^ 2))⁻¹ ∂ν
      ≤ ∫⁻ y, g y ∂ν := lintegral_mono hfg
    _ = ν B + ENNReal.ofReal r⁻¹ * ν B * ∑' k : ℕ, ENNReal.ofReal r ^ k := by rw [hgint, hsum]
    _ < ⊤ := by
        rw [ENNReal.tsum_geometric]
        have hr' : ENNReal.ofReal r < 1 := ENNReal.ofReal_lt_one.2 hr1
        refine ENNReal.add_lt_top.2 ⟨hBfin, ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBfin) ?_⟩
        exact ENNReal.inv_lt_top.2 (tsub_pos_of_lt hr')

end S_NumberField_AdicCompletion_lintegral_inv_max_one_norm_sq_lt_top
end P2MW
export P2MW.S_NumberField_AdicCompletion_lintegral_inv_max_one_norm_sq_lt_top (solution)
