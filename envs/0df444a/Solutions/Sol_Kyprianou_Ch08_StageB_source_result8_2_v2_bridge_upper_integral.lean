-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_upper_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:00:28.668822+00:00
-- url     : https://prove2.me/submissions/79511116-4a31-487b-9166-90b7460064bc

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_strict_exit_clocks_aemeasurable
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
private lemma tauPlus_shift {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (x d : ℝ) (ω : Ω) :
    tauPlus (shifted X x) (x + d) ω = tauPlus X d ω := by
  unfold tauPlus shifted ; congr 1
  ext t ; constructor <;> rintro ⟨u, hu0, hut, hlt⟩ <;> exact ⟨u, hu0, hut, by simpa using hlt⟩
private theorem discountedAt_measurable (q : ℝ) :
    Measurable (fun t : ℝ≥0∞ => discountedAt q t) := by
  have heq : (fun t : ℝ≥0∞ => discountedAt q t) =
      fun t => if t = ⊤ then 0 else Real.exp (-q * t.toReal) := by
    funext t
    induction t using WithTop.recTopCoe with
    | top => exact (if_pos rfl).symm
    | coe s => simp [discountedAt]
  rw [heq]
  exact Measurable.ite (measurableSet_singleton (⊤ : ℝ≥0∞)) measurable_const
    (Real.continuous_exp.measurable.comp (measurable_const.mul ENNReal.measurable_toReal))
private theorem discountedAt_norm_le_one (q : ℝ) (hq : 0 ≤ q) (t : WithTop ℝ≥0) :
    ‖discountedAt q t‖ ≤ 1 := by
  induction t using WithTop.recTopCoe with
  | top => simp [discountedAt]
  | coe s =>
    change ‖Real.exp (-q * (s : ℝ))‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) s.coe_nonneg
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ l d : ℝ, 0 < l → 0 < d →
      ({ω | tauPlus D.X d ω < tauMinus D.X (-l) ω} ⊆
        {ω | NoDrawdownBeforeUpcrossing D.X d (l + d + d) ω}) →
      (∫ ω, (if tauPlus D.X d ω < tauMinus D.X (-l) ω then discountedAt q (tauPlus D.X d ω) else 0) ∂P) ≤
        ∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X d (l + d + d) ω},
          discountedAt q (tauPlus D.X d ω) ∂P := by
  intro l d hl hd hIncl
  have hClock : AEMeasurable (fun ω => (tauPlus D.X d ω : ℝ≥0∞)) P := by
    have hEq : (fun ω => (tauPlus D.X d ω : ℝ≥0∞)) = fun ω => (tauPlus (shifted D.X l) (l + d) ω : ℝ≥0∞) := funext fun ω => (tauPlus_shift D.X l d ω).symm
    rw [hEq]
    exact (source_result81_strict_exit_clocks_aemeasurable Ω P D l (l + d)).1
  have hg : AEStronglyMeasurable (fun ω => discountedAt q (tauPlus D.X d ω)) P :=
    ((discountedAt_measurable q).comp_aemeasurable hClock).aestronglyMeasurable
  have hInt : IntegrableOn (fun ω => discountedAt q (tauPlus D.X d ω)) {ω | NoDrawdownBeforeUpcrossing D.X d (l + d + d) ω} P :=
    IntegrableOn.of_bound (measure_lt_top P _) hg.restrict 1 (Eventually.of_forall fun ω => discountedAt_norm_le_one q hq _)
  have hEq : (∫ ω, (if tauPlus D.X d ω < tauMinus D.X (-l) ω then discountedAt q (tauPlus D.X d ω) else 0) ∂P) = ∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X d (l + d + d) ω}, (if tauPlus D.X d ω < tauMinus D.X (-l) ω then discountedAt q (tauPlus D.X d ω) else 0) ∂P :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun ω hN => if_neg (fun hU => hN (hIncl hU)))).symm
  rw [hEq]
  have hDiscNonneg : ∀ t : WithTop ℝ≥0, 0 ≤ discountedAt q t := by
    intro t
    induction t using WithTop.recTopCoe with
    | top => simp [discountedAt]
    | coe s => simp [discountedAt, Real.exp_nonneg]
  have hF0 : ∀ ω ∈ {ω | NoDrawdownBeforeUpcrossing D.X d (l + d + d) ω}, 0 ≤ (if tauPlus D.X d ω < tauMinus D.X (-l) ω then discountedAt q (tauPlus D.X d ω) else 0) := by
    intro ω _
    by_cases hU : tauPlus D.X d ω < tauMinus D.X (-l) ω
    · rw [if_pos hU] ; exact hDiscNonneg _
    · simp [if_neg hU]
  have hFle : ∀ ω ∈ {ω | NoDrawdownBeforeUpcrossing D.X d (l + d + d) ω}, (if tauPlus D.X d ω < tauMinus D.X (-l) ω then discountedAt q (tauPlus D.X d ω) else 0) ≤ discountedAt q (tauPlus D.X d ω) := by
    intro ω _
    by_cases hU : tauPlus D.X d ω < tauMinus D.X (-l) ω
    · simp [if_pos hU]
    · rw [if_neg hU] ; exact hDiscNonneg _
  exact setIntegral_mono_of_nonneg hF0 hFle hInt
