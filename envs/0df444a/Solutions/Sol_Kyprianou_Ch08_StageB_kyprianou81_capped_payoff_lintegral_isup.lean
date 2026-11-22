-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.kyprianou81_capped_payoff_lintegral_isup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T03:25:49.572029+00:00
-- url     : https://prove2.me/submissions/bf0ec418-2487-470f-aecb-d0bad76cda34

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_lower_passage_event_measurable
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_randomAge_whole_shiftedPath_measurable
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F) (lower upper : ℝ)
    (discountE : ℝ≥0 → ℝ≥0∞) (hdE : Measurable discountE)
    (rewardE : (ℝ≥0 → ℝ) → ℝ≥0∞) (hrE : Measurable rewardE) :
    let U := twoSidedExitUpTime X upper
    let L := twoSidedExitDownTime X lower
    let A : ℕ → Set Ω := fun n => {ω | U ω < L ω} ∩ {ω | U ω ≤ (n : ℝ≥0∞)}
    let τ : ℕ → Ω → ℝ≥0 := fun n ω => (min (U ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal
    let Fc : ℕ → Ω → ℝ≥0∞ := fun n ω => if ω ∈ A n then discountE (τ n ω) *
      rewardE (fun t : ℝ≥0 => X.X (τ n ω + t) ω - X.X (τ n ω) ω) else 0
    (∫⁻ ω, if U ω < L ω then discountE ((U ω).toNNReal) *
      rewardE (fun t : ℝ≥0 => X.X ((U ω).toNNReal + t) ω - X.X ((U ω).toNNReal) ω)
      else 0 ∂P) = ⨆ n, (∫⁻ ω, Fc n ω ∂P) := by
  classical
  let U : Ω → ℝ≥0∞ := twoSidedExitUpTime X upper
  let L : Ω → ℝ≥0∞ := twoSidedExitDownTime X lower
  obtain ⟨hU, -⟩ := chat03_both_named_passage_clocks_measurable X lower upper
  have hEvt : MeasurableSet {ω : Ω | U ω < L ω} :=
    chat03_upper_before_lower_passage_event_measurable X lower upper
  let A : ℕ → Set Ω := fun n => {ω | U ω < L ω} ∩ {ω | U ω ≤ (n : ℝ≥0∞)}
  let τ : ℕ → Ω → ℝ≥0 := fun n ω => (min (U ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal
  let Fc : ℕ → Ω → ℝ≥0∞ := fun n ω => if ω ∈ A n then discountE (τ n ω) *
      rewardE (fun t : ℝ≥0 => X.X (τ n ω + t) ω - X.X (τ n ω) ω) else 0
  have hτm : ∀ n, Measurable (τ n) :=
    fun n => firstRecord_truncation_clock_measurable X upper (n : ℝ≥0)
  have hFm : ∀ n, Measurable (Fc n) := fun n => Measurable.ite
    (hEvt.inter (hU measurableSet_Iic))
    ((hdE.comp (hτm n)).mul (hrE.comp
      (avram_ws01e_b_randomAge_whole_shiftedPath_measurable X (τ n) (hτm n)))) measurable_const
  have hτeq : ∀ n ω, ω ∈ A n → τ n ω = (U ω).toNNReal := fun n ω hn =>
    congrArg ENNReal.toNNReal (min_eq_left (by simpa only [ENNReal.coe_natCast n, Set.mem_setOf_eq] using hn.2))
  have hAmono : ∀ n m, n ≤ m → ∀ ω, ω ∈ A n → ω ∈ A m :=
    fun n m hnm ω hn => ⟨hn.1, Set.mem_setOf_eq.mpr (le_trans (Set.mem_setOf_eq.mp hn.2) (Nat.cast_le.mpr hnm))⟩
  have hFmono : Monotone Fc := fun n m hnm ω =>
    if hn : ω ∈ A n then by
      simp only [Fc, if_pos hn, if_pos (hAmono n m hnm ω hn), hτeq n ω hn,
        hτeq m ω (hAmono n m hnm ω hn), le_refl]
    else by simp [Fc, hn]
  have hEvent : ∀ ω, U ω < L ω → ∃ n, ω ∈ A n := fun ω h =>
    Exists.elim (ENNReal.exists_nat_gt (ne_top_of_lt (lt_of_lt_of_le h le_top)))
      (fun n hn => ⟨n, h, le_of_lt hn⟩)
  have hFsup : ∀ ω, (⨆ n, Fc n ω) = (if U ω < L ω then discountE ((U ω).toNNReal) *
      rewardE (fun t : ℝ≥0 => X.X ((U ω).toNNReal + t) ω - X.X ((U ω).toNNReal) ω) else 0) :=
    fun ω => if h : U ω < L ω then by
      rw [if_pos h]
      obtain ⟨n, hn⟩ := hEvent ω h
      apply le_antisymm
      · apply iSup_le; intro k
        by_cases hk : ω ∈ A k
        · simp only [Fc, if_pos hk, hτeq k ω hk, le_refl]
        · simp [Fc, hk]
      · exact le_iSup_of_le n (by simp only [Fc, if_pos hn, hτeq n ω hn, le_refl])
    else by rw [if_neg h]; simp [Fc, A, h]
  exact (lintegral_congr (fun ω => (hFsup ω).symm)).trans (lintegral_iSup hFm hFmono)
