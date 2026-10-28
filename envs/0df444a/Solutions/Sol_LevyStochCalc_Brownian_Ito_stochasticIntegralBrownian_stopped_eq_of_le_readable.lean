-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_eq_of_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:27:43.860707+00:00
-- url     : https://prove2.me/submissions/f4478487-8fb4-45ad-8b96-c428e3bcf5ad

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLinear
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLocality
import Theorems.Thm_LevyStochCalc_Brownian_Ito_eventually_gridStop_lt_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_gridStopAux_le_iff_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_stopped_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoLinear.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
section Energy
variable {H₁ H₂ : Ω → ℝ → ℝ}
/-- The energy density of an integrand is measurable in the sample point. -/
theorem LevyStochCalc.Brownian.Ito.measurable_energyDensity (hm : Measurable (Function.uncurry H₁)) (T : ℝ) :
    Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
  have hf : Measurable fun p : Ω × ℝ => (‖H₁ p.1 p.2‖₊ : ℝ≥0∞) ^ 2 :=
    (((measurable_nnnorm.comp hm).coe_nnreal_ennreal).pow_const 2)
  exact hf.lintegral_prod_right'
end Energy
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoLocality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  (τ : Ω → WithTop ℝ)
section GridStop
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem LevyStochCalc.Brownian.Ito.le_stepStop (c : ℝ) (ω : Ω) : τ ω ≤ stepStop τ c ω := by
  rw [stepStop]
  split_ifs with h
  · exact le_top
  · exact (not_le.mp h).le
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem LevyStochCalc.Brownian.Ito.stepStop_eq_or (c : ℝ) (ω : Ω) :
    stepStop τ c ω = ((c : ℝ) : WithTop ℝ) ∨ stepStop τ c ω = ⊤ := by
  rw [stepStop]
  split_ifs with h
  · exact Or.inr rfl
  · exact Or.inl rfl
theorem LevyStochCalc.Brownian.Ito.isStoppingTime_stepStop {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (c : ℝ) :
    MeasureTheory.IsStoppingTime ℱ (stepStop τ c) := by
  intro i
  by_cases hci : c ≤ i
  · have hset : {ω | stepStop τ c ω ≤ ((i : ℝ) : WithTop ℝ)}
        = {ω | τ ω < ((c : ℝ) : WithTop ℝ)} := by
      ext ω
      simp only [stepStop, Set.mem_setOf_eq]
      by_cases h : ((c : ℝ) : WithTop ℝ) ≤ τ ω
      · simp only [if_pos h, top_le_iff]
        constructor
        · intro hcon
          exact absurd hcon (by simp)
        · intro hcon
          exact absurd h (not_le.mpr hcon)
      · simp only [if_neg h]
        exact ⟨fun _ => not_le.mp h, fun _ => by exact_mod_cast hci⟩
    rw [hset]
    exact ℱ.mono hci _ (hτ.measurableSet_lt c)
  · have hset : {ω | stepStop τ c ω ≤ ((i : ℝ) : WithTop ℝ)} = ∅ := by
      ext ω
      simp only [stepStop, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      by_cases h : ((c : ℝ) : WithTop ℝ) ≤ τ ω
      · simp only [if_pos h, top_le_iff]
        simp
      · simp only [if_neg h]
        exact fun hcon => hci (by exact_mod_cast hcon)
    rw [hset]
    exact @MeasurableSet.empty Ω (ℱ i)
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem LevyStochCalc.Brownian.Ito.le_gridStopAux (t : ℝ) (n k : ℕ) (ω : Ω) : τ ω ≤ gridStopAux τ t n k ω := by
  induction k with
  | zero => exact le_stepStop τ _ ω
  | succ k ih => exact le_min (le_stepStop τ _ ω) ih
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem LevyStochCalc.Brownian.Ito.gridStopAux_eq (t : ℝ) (n k : ℕ) (ω : Ω) :
    (∃ j ≤ k, gridStopAux τ t n k ω = ((gridPt t n j : ℝ) : WithTop ℝ))
      ∨ gridStopAux τ t n k ω = ⊤ := by
  induction k with
  | zero =>
    rcases stepStop_eq_or τ (gridPt t n 0) ω with h | h
    · exact Or.inl ⟨0, le_rfl, h⟩
    · exact Or.inr h
  | succ k ih =>
    have hval : gridStopAux τ t n (k + 1) ω
        = min (stepStop τ (gridPt t n (k + 1)) ω) (gridStopAux τ t n k ω) := rfl
    rw [hval]
    rcases le_total (stepStop τ (gridPt t n (k + 1)) ω) (gridStopAux τ t n k ω) with h | h
    · rw [min_eq_left h]
      rcases stepStop_eq_or τ (gridPt t n (k + 1)) ω with h1 | h1
      · exact Or.inl ⟨k + 1, le_rfl, h1⟩
      · exact Or.inr h1
    · rw [min_eq_right h]
      rcases ih with ⟨j, hj, hje⟩ | hje
      · exact Or.inl ⟨j, hj.trans (Nat.le_succ k), hje⟩
      · exact Or.inr hje
theorem LevyStochCalc.Brownian.Ito.isStoppingTime_gridStopAux {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (t : ℝ) (n k : ℕ) :
    MeasureTheory.IsStoppingTime ℱ (gridStopAux τ t n k) := by
  intro i
  have hset : {ω | gridStopAux τ t n k ω ≤ ((i : ℝ) : WithTop ℝ)}
      = ⋃ j : Fin (k + 1), {ω | stepStop τ (gridPt t n j) ω ≤ ((i : ℝ) : WithTop ℝ)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, gridStopAux_le_iff_readable]
    constructor
    · rintro ⟨j, hj, hjle⟩
      exact ⟨⟨j, Nat.lt_succ_of_le hj⟩, hjle⟩
    · rintro ⟨j, hjle⟩
      exact ⟨j.1, Nat.lt_succ_iff.mp j.2, hjle⟩
  rw [hset]
  exact MeasurableSet.iUnion fun j => isStoppingTime_stepStop τ hτ (gridPt t n j) i
theorem LevyStochCalc.Brownian.Ito.isStoppingTime_gridStop {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (t : ℝ) (n : ℕ) :
    MeasureTheory.IsStoppingTime ℱ (gridStop τ t n) :=
  isStoppingTime_gridStopAux τ hτ t n n
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem LevyStochCalc.Brownian.Ito.le_gridStop (t : ℝ) (n : ℕ) (ω : Ω) : τ ω ≤ gridStop τ t n ω :=
  le_gridStopAux τ t n n ω
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem LevyStochCalc.Brownian.Ito.gridPt_nonneg {t : ℝ} (ht : 0 ≤ t) (n k : ℕ) : 0 ≤ gridPt t n k := by
  unfold gridPt
  positivity
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem LevyStochCalc.Brownian.Ito.gridPt_lt_of_lt {t : ℝ} (ht : 0 < t) {n k : ℕ} (hk : k < n) : gridPt t n k < t := by
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le k) hk
  rw [gridPt, div_lt_iff₀ hn]
  have hkn : (k : ℝ) < (n : ℝ) := by exact_mod_cast hk
  nlinarith
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem LevyStochCalc.Brownian.Ito.gridPt_self {t : ℝ} {n : ℕ} (hn : n ≠ 0) : gridPt t n n = t := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [gridPt]
  field_simp
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- The grid stopping time takes one of the grid values strictly below `t`, or a value at
least `t`. -/
theorem LevyStochCalc.Brownian.Ito.gridStop_finiteRange {t : ℝ} {n : ℕ} (hn : n ≠ 0) (ω : Ω) :
    (∃ c ∈ (Finset.range n).image (gridPt t n),
        gridStop τ t n ω = ((c : ℝ) : WithTop ℝ))
      ∨ ((t : ℝ) : WithTop ℝ) ≤ gridStop τ t n ω := by
  rcases gridStopAux_eq τ t n n ω with ⟨j, hj, hje⟩ | hje
  · rcases lt_or_eq_of_le hj with hlt | rfl
    · exact Or.inl ⟨gridPt t n j, Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hlt, rfl⟩, hje⟩
    · refine Or.inr ?_
      rw [gridStop, hje, gridPt_self hn]
  · exact Or.inr (by rw [gridStop, hje]; exact le_top)
end GridStop
section Local
variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
open LevyStochCalc.Brownian.Ito in
include hℱ in
/-- **The local property of the Itô integral.** At a time the stopping time has not reached,
cutting the integrand off at it changes nothing. -/
theorem solution
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
    (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ ω →
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Probability.stopped τ H)
          (LevyStochCalc.Probability.measurable_uncurry_stopped hτ hm)
          (LevyStochCalc.Probability.ProgressivelyMeasurable.stopped hτ hp)
          (LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (fun ω s => LevyStochCalc.Probability.abs_stopped_le τ H ω s) hq) t ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω := by
  classical
  -- the cut integrand and its approximations
  have hmS := LevyStochCalc.Probability.measurable_uncurry_stopped hτ hm
  have hpS := LevyStochCalc.Probability.ProgressivelyMeasurable.stopped hτ hp
  have hqS := LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (P := P) (fun ω s => LevyStochCalc.Probability.abs_stopped_le τ H ω s) hq
  have hmG : ∀ n : ℕ, Measurable (Function.uncurry
      (LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H)) :=
    fun n => LevyStochCalc.Probability.measurable_uncurry_stopped (LevyStochCalc.Brownian.Ito.isStoppingTime_gridStop τ hτ t n) hm
  have hpG : ∀ n : ℕ, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
      (LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H) :=
    fun n => LevyStochCalc.Probability.ProgressivelyMeasurable.stopped (LevyStochCalc.Brownian.Ito.isStoppingTime_gridStop τ hτ t n) hp
  have hqG : ∀ (n : ℕ) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun n => LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (P := P)
      (fun ω s => LevyStochCalc.Probability.abs_stopped_le (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s) hq
  -- the event on which the stopping time has not been reached
  set A : Set Ω := {ω | ((t : ℝ) : WithTop ℝ) ≤ τ ω} with hAdef
  have hAmeas : MeasurableSet A := by
    have hcompl : A = {ω | τ ω < ((t : ℝ) : WithTop ℝ)}ᶜ := by
      ext ω
      simp only [hAdef, Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
    rw [hcompl]
    exact (ℱ.le t _ (hτ.measurableSet_lt t)).compl
  -- on that event the approximations already agree with the uncut integral
  have hagree : ∀ n : ℕ, n ≠ 0 → ∀ᵐ ω ∂P, ω ∈ A →
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H)
          (hmG n) (hpG n) (hqG n) t ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω := by
    intro n hn
    have hid := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_readable (LevyStochCalc.Brownian.Ito.gridStop τ t n) W ℱ hℱ
      (LevyStochCalc.Brownian.Ito.isStoppingTime_gridStop τ hτ t n) hm hp hq ht
      ((Finset.range n).image (LevyStochCalc.Brownian.Ito.gridPt t n))
      (by
        intro c hc
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
        exact LevyStochCalc.Brownian.Ito.gridPt_nonneg ht.le n k)
      (by
        intro c hc
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
        exact LevyStochCalc.Brownian.Ito.gridPt_lt_of_lt ht (Finset.mem_range.mp hk))
      (LevyStochCalc.Brownian.Ito.gridStop_finiteRange τ hn)
    filter_upwards [hid] with ω hω hωA
    rw [hω]
    have hzero : ∀ c ∈ (Finset.range n).image (LevyStochCalc.Brownian.Ito.gridPt t n),
        LevyStochCalc.Brownian.Ito.hitInd (LevyStochCalc.Brownian.Ito.gridStop τ t n) c ω = 0 := by
      intro c hc
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
      have hlt : LevyStochCalc.Brownian.Ito.gridPt t n k < t := LevyStochCalc.Brownian.Ito.gridPt_lt_of_lt ht (Finset.mem_range.mp hk)
      have hne : LevyStochCalc.Brownian.Ito.gridStop τ t n ω ≠ ((LevyStochCalc.Brownian.Ito.gridPt t n k : ℝ) : WithTop ℝ) := by
        intro hcon
        have h1 : ((t : ℝ) : WithTop ℝ) ≤ ((LevyStochCalc.Brownian.Ito.gridPt t n k : ℝ) : WithTop ℝ) :=
          le_trans hωA (le_trans (LevyStochCalc.Brownian.Ito.le_gridStop τ t n ω) (le_of_eq hcon))
        exact absurd (by exact_mod_cast h1 : t ≤ gridPt t n k) (not_le.mpr hlt)
      simp [LevyStochCalc.Brownian.Ito.hitInd, Set.indicator_of_notMem (show ω ∉ {ω | LevyStochCalc.Brownian.Ito.gridStop τ t n ω
        = ((LevyStochCalc.Brownian.Ito.gridPt t n k : ℝ) : WithTop ℝ)} from hne)]
    have hsum : ∑ c ∈ (Finset.range n).image (LevyStochCalc.Brownian.Ito.gridPt t n),
        LevyStochCalc.Brownian.Ito.hitInd (LevyStochCalc.Brownian.Ito.gridStop τ t n) c ω
          * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq c ω) = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      rw [hzero c hc, zero_mul]
    rw [hsum, sub_zero]
  -- the approximations converge to the cut integrand in energy
  have hEtend : Filter.Tendsto (fun n : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s
        - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) Filter.atTop (𝓝 0) := by
    have hbmeas : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := LevyStochCalc.Brownian.Ito.measurable_energyDensity hm t
    have hFmeas : ∀ n : ℕ, Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s
          - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
      fun n => LevyStochCalc.Brownian.Ito.measurable_energyDensity ((hmG n).sub hmS) t
    have hptw : ∀ (n : ℕ) (ω : Ω) (s : ℝ),
        (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s
          - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ≤ (‖H ω s‖₊ : ℝ≥0∞) ^ 2 := by
      intro n ω s
      have habs : |LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s - LevyStochCalc.Probability.stopped τ H ω s|
          ≤ |H ω s| := by
        rw [LevyStochCalc.Probability.stopped, LevyStochCalc.Probability.stopped]
        by_cases h1 : ((s : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Brownian.Ito.gridStop τ t n ω
        · by_cases h2 : ((s : ℝ) : WithTop ℝ) ≤ τ ω
          · simp [h1, h2]
          · simp [h1, h2]
        · have h2 : ¬ ((s : ℝ) : WithTop ℝ) ≤ τ ω := fun hcon =>
            h1 (le_trans hcon (LevyStochCalc.Brownian.Ito.le_gridStop τ t n ω))
          simp [h1, h2]
      have hle : (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s
          - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ≤ (‖H ω s‖₊ : ℝ≥0∞) := by
        refine ENNReal.coe_le_coe.mpr ?_
        rw [← NNReal.coe_le_coe]
        simpa [Real.norm_eq_abs] using habs
      gcongr
    have hinner : ∀ᵐ ω ∂P, Filter.Tendsto (fun n : ℕ => ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s
          - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) Filter.atTop (𝓝 0) := by
      filter_upwards [MeasureTheory.ae_lt_top hbmeas (hq t ht).ne] with ω hfin
      have hlims : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
          Filter.Tendsto (fun n : ℕ =>
            (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s
              - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2) Filter.atTop (𝓝 0) := by
        have hnull : (volume.restrict (Set.Icc (0 : ℝ) t)) {(0 : ℝ)} = 0 := by
          simp
        filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull,
          MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs0 hsmem
        have hsne : s ≠ 0 := by simpa using hs0
        have hs : 0 < s := lt_of_le_of_ne hsmem.1 (Ne.symm hsne)
        by_cases hτs : ((s : ℝ) : WithTop ℝ) ≤ τ ω
        · refine tendsto_atTop_of_eventually_const (i₀ := 0) fun n _ => ?_
          have h1 : ((s : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Brownian.Ito.gridStop τ t n ω :=
            le_trans hτs (LevyStochCalc.Brownian.Ito.le_gridStop τ t n ω)
          simp [LevyStochCalc.Probability.stopped, h1, hτs]
        · rw [not_le] at hτs
          obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
            (LevyStochCalc.Brownian.Ito.eventually_gridStop_lt_readable τ ht ω hs hsmem.2 hτs)
          refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
          have h1 : ¬ ((s : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Brownian.Ito.gridStop τ t n ω := not_le.mpr (hN n hn)
          have h2 : ¬ ((s : ℝ) : WithTop ℝ) ≤ τ ω := not_le.mpr hτs
          simp [LevyStochCalc.Probability.stopped, h1, h2]
      have hconv := MeasureTheory.tendsto_lintegral_of_dominated_convergence
        (μ := volume.restrict (Set.Icc (0 : ℝ) t))
        (F := fun n s => (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s
          - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2)
        (f := fun _ : ℝ => (0 : ℝ≥0∞))
        (bound := fun s => (‖H ω s‖₊ : ℝ≥0∞) ^ 2)
        (fun n => ((((hmG n).sub hmS).comp measurable_prodMk_left).nnnorm.coe_nnreal_ennreal
          ).pow_const 2)
        (fun n => Filter.Eventually.of_forall fun s => hptw n ω s) hfin.ne hlims
      simpa using hconv
    have hconv := MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (F := fun n ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s
          - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      (f := fun _ : Ω => (0 : ℝ≥0∞))
      (bound := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      hFmeas
      (fun n => Filter.Eventually.of_forall fun ω =>
        lintegral_mono fun s => hptw n ω s)
      (hq t ht).ne hinner
    simpa using hconv
  -- the squeeze
  set D : Ω → ℝ≥0∞ := fun ω => A.indicator (fun ω =>
    (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Probability.stopped τ H) hmS hpS hqS t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω‖₊ : ℝ≥0∞) ^ 2) ω with hDdef
  have hSImeas : ∀ {K : Ω → ℝ → ℝ} (hmK : Measurable (Function.uncurry K))
      (hpK : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ K)
      (hqK : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      Measurable (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hmK hpK hqK t) := by
    intro K hmK hpK hqK
    exact ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ K hmK hpK hqK t).mono
      (ℱ.le t)).measurable
  have hDmeas : Measurable D := by
    refine Measurable.indicator ?_ hAmeas
    exact ((((hSImeas hmS hpS hqS).sub (hSImeas hm hp hq)).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hDle : ∀ n : ℕ, n ≠ 0 → ∫⁻ ω, D ω ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s
          - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    intro n hn
    rw [← LevyStochCalc.Brownian.Ito.isometry_diff_stochasticIntegralBrownian W ℱ hℱ
      (LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H) (LevyStochCalc.Probability.stopped τ H)
      (hmG n) hmS (hpG n) hpS (hqG n) hqS ht]
    refine lintegral_mono_ae ?_
    filter_upwards [hagree n hn] with ω hω
    by_cases hωA : ω ∈ A
    · simp only [hDdef]
      have hrev : ∀ x y : ℝ, ‖x - y‖₊ = ‖y - x‖₊ := by
        intro x y
        rw [← NNReal.coe_inj]
        simpa using norm_sub_rev x y
      rw [Set.indicator_of_mem hωA, hω hωA, hrev]
    · simp only [hDdef]
      rw [Set.indicator_of_notMem hωA]
      exact zero_le
  have hDzero : ∫⁻ ω, D ω ∂P = 0 := by
    refine le_antisymm ?_ zero_le
    refine ge_of_tendsto hEtend ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    exact hDle n hn.ne'
  have hDae := (MeasureTheory.lintegral_eq_zero_iff hDmeas).mp hDzero
  filter_upwards [hDae] with ω hω hωA
  have h0 : D ω = 0 := hω
  simp only [hDdef] at h0
  rw [Set.indicator_of_mem (show ω ∈ A from hωA)] at h0
  have hnn : (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Probability.stopped τ H) hmS hpS hqS t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω‖₊ : ℝ≥0∞) = 0 := by
    simpa [pow_eq_zero_iff] using h0
  have : ‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Probability.stopped τ H) hmS hpS hqS t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω‖₊ = 0 := by
    exact_mod_cast hnn
  have hsub : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Probability.stopped τ H) hmS hpS hqS t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω = 0 := by
    simpa using this
  linarith [hsub]
