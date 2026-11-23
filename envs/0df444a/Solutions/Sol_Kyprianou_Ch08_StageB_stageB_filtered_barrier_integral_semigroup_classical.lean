-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.stageB_filtered_barrier_integral_semigroup_classical
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T05:08:03.573178+00:00
-- url     : https://prove2.me/submissions/91bacb47-5b1b-44d8-be02-ed3e2de0c4a8

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_stageB_Bars
import Definitions.Def_stageB_bpay
import Theorems.Thm_stageB_actual_height_barrier_semigroup
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable
import Theorems.Thm_AvramDividend_Classical_upperPassage_measurable_from_stopping
import Theorems.Thm_stageB_tauPlus_coe_eq
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped Classical NNReal ENNReal

private theorem integral_toReal_eq_lintegral_of_measurable_ne_top {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {f : Ω → ℝ≥0∞} (hf : Measurable f) (hne : ∀ ω, f ω ≠ ∞) :
    (∫ ω, (f ω).toReal ∂P) = (∫⁻ ω, f ω ∂P).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (μ := P) (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) ((ENNReal.measurable_toReal.comp hf).aestronglyMeasurable)]
  congr 1
  exact lintegral_congr_ae (Eventually.of_forall fun ω => ENNReal.ofReal_toReal (hne ω))

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (a1 a2 h q c1 c2 c12 : ℝ)
    (ha1 : 0 < a1) (ha2 : 0 < a2) (hh : 0 < h) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hc12 : 0 ≤ c12) (hmul : c12 = c1 * c2)
    (hIS : ∀ (b : ℝ) (hb : 0 < b) (ω : Ω), (⨆ r : stageB_Bars h, stageB_bpay X (r : ℝ) b q ω) = if twoSidedExitUpTime X b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing X.X b h ω then ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal))) else 0) :
    (∫ ω, (ENNReal.ofReal c12 * (⨆ r : stageB_Bars h, stageB_bpay X (r : ℝ) (a1 + a2) q ω)).toReal ∂P) =
    (∫ ω, (ENNReal.ofReal c1 * (⨆ r : stageB_Bars h, stageB_bpay X (r : ℝ) a1 q ω)).toReal ∂P) * (∫ ω, (ENNReal.ofReal c2 * (⨆ r : stageB_Bars h, stageB_bpay X (r : ℝ) a2 q ω)).toReal ∂P) := by
  classical
  let I := stageB_Bars h
  let p : ℝ → I → Ω → ℝ≥0∞ := fun b r ω => stageB_bpay X (r : ℝ) b q ω
  let J : ℝ → I → ℝ≥0∞ := fun b r => ∫⁻ ω, p b r ω ∂P
  have Fm (b : ℝ) (r : I) : Measurable (p b r) := by
    have hU := upperPassage_measurable_from_stopping X b
    dsimp [p, stageB_bpay]
    exact Measurable.ite
      (measurableSet_lt hU (barrierRuinTime_measurable X (r : ℝ)))
      (by measurability) measurable_const
  have MonoP (b : ℝ) {r s : I} (hrs : (r : ℝ) ≤ (s : ℝ)) : p b r ≤ p b s := by
    intro ω
    dsimp [p]
    unfold stageB_bpay
    by_cases hr : twoSidedExitUpTime X b ω < barrierRuinTime X (r : ℝ) ω
    · simp [hr, lt_of_lt_of_le hr (barrierRuinTime_mono_barrier X (r : ℝ) (s : ℝ) hrs ω)]
    · simp [hr]
  have Mono (b : ℝ) {r s : I} (hrs : (r : ℝ) ≤ (s : ℝ)) : J b r ≤ J b s := by
    simpa only [J] using lintegral_mono (MonoP b hrs)
  have Pick (r s : I) : ∃ u : I, (r : ℝ) ≤ (u : ℝ) ∧ (s : ℝ) ≤ (u : ℝ) := by
    obtain ⟨t, hrt, hth⟩ := exists_rat_btwn (max_lt r.2.2 s.2.2)
    exact ⟨⟨t, lt_trans r.2.1 (lt_of_le_of_lt (le_max_left _ _) hrt), hth⟩,
      le_trans (le_max_left _ _) hrt.le, le_trans (le_max_right _ _) hrt.le⟩
  have Lin (b : ℝ) : (∫⁻ ω, ⨆ r : I, p b r ω ∂P) = ⨆ r : I, J b r := by
    apply lintegral_iSup_directed_of_measurable (fun r => Fm b r)
    intro r s
    obtain ⟨u, hr, hs⟩ := Pick r s
    exact ⟨u, MonoP b hr, MonoP b hs⟩
  have SL (b cc : ℝ) : (∫⁻ ω, ENNReal.ofReal cc * (⨆ r : I, p b r ω) ∂P) = ENNReal.ofReal cc * (⨆ r : I, J b r) := by
    rw [lintegral_const_mul _ (Measurable.iSup fun r => Fm b r), Lin b]
  have hs (r : I) : J (a1 + a2) r = J a1 r * J a2 r := by
    dsimp [J, p]
    exact stageB_actual_height_barrier_semigroup X (r : ℝ) a1 a2 q r.2.1 ha1 ha2
  have Diag : (⨆ r : I, J (a1 + a2) r) = (⨆ r : I, J a1 r) * (⨆ r : I, J a2 r) := by
    simp_rw [hs]
    apply le_antisymm
    · exact iSup_le fun r => mul_le_mul (le_iSup (J a1) r) (le_iSup (J a2) r) zero_le zero_le
    · rw [ENNReal.iSup_mul]
      refine iSup_le fun r => ?_
      rw [ENNReal.mul_iSup]
      refine iSup_le fun s => ?_
      obtain ⟨u, hr, ht⟩ := Pick r s
      exact (mul_le_mul (Mono a1 hr) (Mono a2 ht) zero_le zero_le).trans
        (le_iSup (fun t : I => J a1 t * J a2 t) u)
  have hOf : ENNReal.ofReal c12 = ENNReal.ofReal c1 * ENNReal.ofReal c2 := by
    rw [hmul, ENNReal.ofReal_mul hc1]
  have EL : (∫⁻ ω, ENNReal.ofReal c12 * (⨆ r : I, p (a1 + a2) r ω) ∂P) = (∫⁻ ω, ENNReal.ofReal c1 * (⨆ r : I, p a1 r ω) ∂P) * (∫⁻ ω, ENNReal.ofReal c2 * (⨆ r : I, p a2 r ω) ∂P) := by
    rw [SL (a1 + a2) c12, SL a1 c1, SL a2 c2, Diag, hOf]
    ac_rfl
  have MK (b cc : ℝ) : Measurable (fun ω => ENNReal.ofReal cc * (⨆ r : I, p b r ω)) := measurable_const.mul (Measurable.iSup fun r => Fm b r)
  have RK (b cc : ℝ) (hb : 0 < b) : (∫ ω, (ENNReal.ofReal cc * (⨆ r : I, p b r ω)).toReal ∂P) = (∫⁻ ω, ENNReal.ofReal cc * (⨆ r : I, p b r ω) ∂P).toReal :=
    integral_toReal_eq_lintegral_of_measurable_ne_top (P := P)
      (f := fun ω => ENNReal.ofReal cc * (⨆ r : I, p b r ω)) (MK b cc)
      (by
        intro ω
        simp only [p, I, hIS b hb ω]
        split_ifs
        · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
        · simp)
  simpa [ENNReal.toReal_mul, ← RK (a1 + a2) c12 (add_pos ha1 ha2), ← RK a1 c1 ha1, ← RK a2 c2 ha2, p, I] using congrArg ENNReal.toReal EL
