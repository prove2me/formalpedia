-- Prove2me | solution 1 for MarkovProcess.IsKolmogorovProcess.ae_cauchySeq_unitDyadicFloorValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:33:11.933668+00:00
-- url     : https://prove2.me/submissions/3aefdc4d-1aa3-4cef-9fd3-ba2fc4065146

import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicFloor
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov
import Theorems.Thm_MarkovProcess_edist_unitDyadicGrid_ancestor_le_sum_of_child_parent_le
import Theorems.Thm_MarkovProcess_edist_unitDyadicGrid_child_parent_le_of_adjacent_le
import Theorems.Thm_MarkovProcess_tendsto_dyadicIncrementThreshold_ancestor_tail_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-grid increment bounds

This file supplies the finite union-bound step in a Kolmogorov--Chentsov argument. It is
independent of a particular dyadic-grid encoding: a later specialization only has to bound the
distance between adjacent grid times.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]








theorem IsKolmogorovProcess.measure_finiteGridBadIncrement_le_inlineV3
    {T : Type*} [PseudoEMetricSpace T] {N : ℕ} {P : Measure Ω}
    {X : T → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M)
    (grid : Fin (N + 1) → T) (δ ε : ℝ≥0∞)
    (hgrid : ∀ i : Fin N, edist (grid i.castSucc) (grid i.succ) ≤ δ)
    (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞) :
    P (finiteGridBadIncrement X grid p ε) ≤ N * (M * δ ^ q / ε ^ p) := by
  unfold finiteGridBadIncrement
  calc
    P (⋃ i : Fin N,
        {ω | ε ^ p ≤ edist (X (grid i.castSucc) ω) (X (grid i.succ) ω) ^ p}) ≤
        ∑ i : Fin N,
          P {ω | ε ^ p ≤ edist (X (grid i.castSucc) ω) (X (grid i.succ) ω) ^ p} :=
      measure_iUnion_fintype_le P _
    _ ≤ ∑ _i : Fin N, (M * δ ^ q / ε ^ p) := by
      apply Finset.sum_le_sum
      intro i _hi
      calc
        P {ω | ε ^ p ≤ edist (X (grid i.castSucc) ω) (X (grid i.succ) ω) ^ p} ≤
            (∫⁻ ω, edist (X (grid i.castSucc) ω) (X (grid i.succ) ω) ^ p ∂P) /
              ε ^ p := by
          apply meas_ge_le_lintegral_div
          · exact (hX.measurable_edist.pow_const p).aemeasurable
          · exact (ENNReal.rpow_eq_zero_iff_of_pos hX.p_pos).not.mpr hε0
          · exact (ENNReal.rpow_eq_top_iff_of_pos hX.p_pos).not.mpr hεtop
        _ ≤ (M * δ ^ q) / ε ^ p := by
          gcongr
          exact (hX.kolmogorovCondition _ _).trans
            (mul_le_mul_right (ENNReal.rpow_le_rpow (hgrid i) hX.q_pos.le) M)
    _ = N * (M * δ ^ q / ε ^ p) := by simp


theorem dyadic_bound_normalization_inlineV3 (p q γ : ℝ) (M : ℝ≥0) (n : ℕ) :
    (2 : ℝ≥0∞) ^ n *
        ((M : ℝ≥0∞) * (((2 : ℝ≥0∞) ^ n)⁻¹) ^ q /
          dyadicIncrementThreshold γ n ^ p) =
      ((M * dyadicIncrementDecayRatio p q γ ^ n : ℝ≥0) : ℝ≥0∞) := by
  have hl : (2 : ℝ≥0∞) ^ n *
        ((M : ℝ≥0∞) * (((2 : ℝ≥0∞) ^ n)⁻¹) ^ q /
          dyadicIncrementThreshold γ n ^ p) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · simp
    apply ENNReal.div_ne_top
    · apply ENNReal.mul_ne_top
      · simp
      exact ENNReal.rpow_ne_top_of_ne_zero (by simp) (by simp)
    exact ENNReal.rpow_eq_zero_iff.not.mpr (by
      unfold dyadicIncrementThreshold
      simp)
  have hr : ((M * dyadicIncrementDecayRatio p q γ ^ n : ℝ≥0) : ℝ≥0∞) ≠ ∞ := by
    finiteness
  apply (ENNReal.toReal_eq_toReal_iff' hl hr).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ENNReal.toReal_div, ENNReal.coe_toReal, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_rpow,
    dyadicIncrementThreshold, dyadicIncrementDecayRatio]
  rw [← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  simp [← Real.rpow_natCast, ← Real.rpow_mul]
  rw [← Real.rpow_neg (by positivity), ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul (by positivity), div_eq_mul_inv,
    ← Real.rpow_neg (by positivity), ← Real.rpow_mul (by positivity)]
  calc
    2 ^ (n : ℝ) * ((M : ℝ) * 2 ^ (-(n : ℝ) * q) * 2 ^ (-(n : ℝ) * -(γ * p))) =
        (M : ℝ) * (2 ^ (n : ℝ) * 2 ^ (-(n : ℝ) * q) *
          2 ^ (-(n : ℝ) * -(γ * p))) := by ring_nf
    _ = (M : ℝ) * 2 ^ ((n : ℝ) + (-(n : ℝ) * q) + (-(n : ℝ) * -(γ * p))) := by
      rw [Real.rpow_add (by positivity), Real.rpow_add (by positivity)]
    _ = (M : ℝ) * 2 ^ ((1 - q + p * γ) * (n : ℝ)) := by
      congr 1
      ring_nf


/-- Adjacent points of the level-`n` unit dyadic grid are at most `2⁻ⁿ` apart. -/
theorem unitDyadicGrid_edist_adjacent_le (n : ℕ) (i : Fin (2 ^ n)) :
    edist (unitDyadicGrid n i.castSucc) (unitDyadicGrid n i.succ) ≤
      ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [edist_dist, ENNReal.ofReal_le_iff_le_toReal]
  · rw [NNRat.dist_eq, Rat.dist_eq]
    simp only [unitDyadicGrid]
    push_cast
    rw [div_sub_div_same]
    simp only [Fin.val_castSucc, Fin.val_succ]
    push_cast
    norm_num [abs_div, abs_of_nonneg]
  · simp

/-- The Kolmogorov finite-grid bound on the level-`n` unit dyadic grid. -/
theorem IsKolmogorovProcess.measure_unitDyadicGridBadIncrement_le
    {P : Measure Ω} {X : NNRat → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (n : ℕ) (ε : ℝ≥0∞)
    (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞) :
    P (finiteGridBadIncrement X (unitDyadicGrid n) p ε) ≤
      2 ^ n * (M * (((2 : ℝ≥0∞) ^ n)⁻¹) ^ q / ε ^ p) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    IsKolmogorovProcess.measure_finiteGridBadIncrement_le_inlineV3 hX (unitDyadicGrid n) _ ε
      (unitDyadicGrid_edist_adjacent_le n) hε0 hεtop
end MarkovProcess

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dyadic increment bounds for the Kolmogorov--Chentsov argument

This file merges the following former modules, one section each:

* `DyadicIncrementSummability`: Geometric summability for dyadic increment bounds
* `DyadicBorelCantelli`: Borel--Cantelli for dyadic increment events
* `DyadicIncrementControl`: Almost-sure control of adjacent dyadic increments
* `DyadicThresholdTail`: Geometric tails of dyadic increment thresholds
-/

namespace MarkovProcess

section DyadicIncrementSummability

open scoped ENNReal NNReal




/-- The admissible Hölder-exponent inequality makes the dyadic ratio strictly less than one. -/
theorem dyadicIncrementDecayRatio_lt_one {p q γ : ℝ} (hp : 0 < p)
    (hγ : γ < (q - 1) / p) : dyadicIncrementDecayRatio p q γ < 1 := by
  have hmul : p * γ < q - 1 := by
    simpa only [mul_comm] using (lt_div_iff₀ hp).mp hγ
  have hexp : 1 - q + p * γ < 0 := by
    linarith only [hmul]
  exact NNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp

/-- The geometric majorant for the dyadic bad-event probabilities is summable. -/
theorem summable_dyadicIncrementDecayRatio {p q γ : ℝ} (M : ℝ≥0) (hp : 0 < p)
    (hγ : γ < (q - 1) / p) :
    Summable (fun n : ℕ ↦ M * dyadicIncrementDecayRatio p q γ ^ n) :=
  (NNReal.summable_geometric (dyadicIncrementDecayRatio_lt_one hp hγ)).mul_left M

/-- The same geometric majorant has finite `ENNReal` total mass, as needed by the first
Borel--Cantelli lemma. -/
theorem tsum_coe_dyadicIncrementDecayRatio_ne_top {p q γ : ℝ} (M : ℝ≥0)
    (hp : 0 < p) (hγ : γ < (q - 1) / p) :
    (∑' n : ℕ, ((M * dyadicIncrementDecayRatio p q γ ^ n : ℝ≥0) : ℝ≥0∞)) ≠ ∞ := by
  rw [ENNReal.tsum_coe_ne_top_iff_summable]
  exact summable_dyadicIncrementDecayRatio M hp hγ

end DyadicIncrementSummability

section DyadicBorelCantelli

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]



theorem dyadicIncrementThreshold_ne_zero {γ : ℝ} (hγ : 0 < γ) (n : ℕ) :
    dyadicIncrementThreshold γ n ≠ 0 := by
  unfold dyadicIncrementThreshold
  exact (ENNReal.rpow_eq_zero_iff_of_pos hγ).not.mpr (by simp)

theorem dyadicIncrementThreshold_ne_top {γ : ℝ} (hγ : 0 < γ) (n : ℕ) :
    dyadicIncrementThreshold γ n ≠ ∞ := by
  unfold dyadicIncrementThreshold
  exact (ENNReal.rpow_eq_top_iff_of_pos hγ).not.mpr (by simp)



/-- The dyadic bad-increment event has a summable geometric majorant. -/
theorem IsKolmogorovProcess.measure_unitDyadicGridBadIncrement_threshold_le
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ) (n : ℕ) :
    P (finiteGridBadIncrement X (unitDyadicGrid n) p (dyadicIncrementThreshold γ n)) ≤
      ((M * dyadicIncrementDecayRatio p q γ ^ n : ℝ≥0) : ℝ≥0∞) := by
  rw [← dyadic_bound_normalization_inlineV3]
  exact IsKolmogorovProcess.measure_unitDyadicGridBadIncrement_le hX n _
    (dyadicIncrementThreshold_ne_zero hγ n) (dyadicIncrementThreshold_ne_top hγ n)

/-- The measures of the dyadic bad-increment events have finite total mass. -/
theorem IsKolmogorovProcess.tsum_measure_unitDyadicGridBadIncrement_threshold_ne_top
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    (∑' n : ℕ,
      P (finiteGridBadIncrement X (unitDyadicGrid n) p (dyadicIncrementThreshold γ n))) ≠ ∞ := by
  exact ne_top_of_le_ne_top
    (tsum_coe_dyadicIncrementDecayRatio_ne_top M hX.p_pos hγq)
    (ENNReal.tsum_le_tsum fun n ↦
      IsKolmogorovProcess.measure_unitDyadicGridBadIncrement_threshold_le hX hγ n)

/-- Almost surely, all sufficiently fine unit dyadic grids avoid the bad-increment event. -/
theorem IsKolmogorovProcess.ae_eventually_notMem_unitDyadicGridBadIncrement_threshold
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ᶠ n in Filter.atTop,
      ω ∉ finiteGridBadIncrement X (unitDyadicGrid n) p (dyadicIncrementThreshold γ n) :=
  MeasureTheory.ae_eventually_notMem
    (IsKolmogorovProcess.tsum_measure_unitDyadicGridBadIncrement_threshold_ne_top
      hX hγ hγq)

end DyadicBorelCantelli

section DyadicIncrementControl

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

/-- Outside the finite-grid bad event, every adjacent increment is strictly below the
specified threshold. -/
theorem edist_adjacent_lt_of_notMem_finiteGridBadIncrement
    {N : ℕ} {T : Type*} {X : T → Ω → E} {grid : Fin (N + 1) → T}
    {p : ℝ} (hp : 0 < p) {ε : ℝ≥0∞} {ω : Ω}
    (hω : ω ∉ finiteGridBadIncrement X grid p ε) (i : Fin N) :
    edist (X (grid i.castSucc) ω) (X (grid i.succ) ω) < ε := by
  rw [← ENNReal.rpow_lt_rpow_iff hp]
  exact lt_of_not_ge fun hi ↦ hω (Set.mem_iUnion.mpr ⟨i, hi⟩)

/-- Almost surely, every adjacent increment on every sufficiently fine unit dyadic grid is
strictly below the level's Kolmogorov--Chentsov threshold. -/
theorem IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_adjacent_lt_threshold
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ᶠ n in Filter.atTop, ∀ i : Fin (2 ^ n),
      edist (X (unitDyadicGrid n i.castSucc) ω)
          (X (unitDyadicGrid n i.succ) ω) < dyadicIncrementThreshold γ n := by
  filter_upwards
    [IsKolmogorovProcess.ae_eventually_notMem_unitDyadicGridBadIncrement_threshold
      hX hγ hγq] with ω hω
  filter_upwards [hω] with n hn
  intro i
  exact edist_adjacent_lt_of_notMem_finiteGridBadIncrement hX.p_pos hn i

end DyadicIncrementControl

section DyadicThresholdTail

open scoped ENNReal NNReal




/-- The level-`n` threshold is the `n`th power of the one-level decay ratio. -/
theorem dyadicIncrementThreshold_eq_ratio_pow (γ : ℝ) (n : ℕ) :
    dyadicIncrementThreshold γ n = dyadicIncrementThresholdRatio γ ^ n := by
  unfold dyadicIncrementThreshold dyadicIncrementThresholdRatio
  rw [ENNReal.inv_rpow, ← ENNReal.rpow_natCast_mul, ← ENNReal.rpow_neg,
    ← ENNReal.rpow_mul_natCast]
  congr 2
  ring



/-- The infinite tail beginning at level `n` has the exact geometric-series value. -/
theorem tsum_dyadicIncrementThreshold_add (γ : ℝ) (n : ℕ) :
    (∑' k : ℕ, dyadicIncrementThreshold γ (n + k)) =
      dyadicIncrementThreshold γ n * (1 - dyadicIncrementThresholdRatio γ)⁻¹ := by
  simp_rw [dyadicIncrementThreshold_eq_ratio_pow, pow_add]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]



/-- Every finite tail segment is bounded by the corresponding infinite geometric tail. -/
theorem sum_dyadicIncrementThreshold_add_le (γ : ℝ) (n N : ℕ) :
    ∑ k ∈ Finset.range N, dyadicIncrementThreshold γ (n + k) ≤
      dyadicIncrementThreshold γ n * (1 - dyadicIncrementThresholdRatio γ)⁻¹ := by
  calc
    ∑ k ∈ Finset.range N, dyadicIncrementThreshold γ (n + k) ≤
        ∑' k : ℕ, dyadicIncrementThreshold γ (n + k) :=
      ENNReal.sum_le_tsum (Finset.range N)
    _ = dyadicIncrementThreshold γ n *
        (1 - dyadicIncrementThresholdRatio γ)⁻¹ :=
      tsum_dyadicIncrementThreshold_add γ n
end DyadicThresholdTail
end MarkovProcess

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Chaining across unit dyadic grids

This file merges the following former modules, one section each:

* `DyadicGridChaining`: Same-level chaining on dyadic grids
* `DyadicMultiscale`: Refinement and parent comparison for unit dyadic grids
* `DyadicAncestorChaining`: Finite chains of dyadic ancestors
* `DyadicAncestorTail`: Uniform tail bounds for finite dyadic ancestor chains
-/

namespace MarkovProcess

section DyadicGridChaining

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]





end DyadicGridChaining

section DyadicMultiscale

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]









@[simp]
theorem unitDyadicParentIndex_val (n : ℕ) (i : Fin (2 ^ (n + 1) + 1)) :
    (unitDyadicParentIndex n i).val = i.val / 2 :=
  rfl









/-- Almost surely, on all sufficiently fine consecutive dyadic levels, every child is
within the fine level's Kolmogorov--Chentsov threshold of its canonical parent. -/
theorem IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_child_parent_le_threshold
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ᶠ n in Filter.atTop, ∀ i : Fin (2 ^ (n + 1) + 1),
      edist (X (unitDyadicGrid (n + 1) i) ω)
          (X (unitDyadicGrid n (unitDyadicParentIndex n i)) ω) ≤
        dyadicIncrementThreshold γ (n + 1) := by
  filter_upwards
    [IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_adjacent_lt_threshold
      hX hγ hγq] with ω hω
  rw [Filter.eventually_atTop] at hω ⊢
  obtain ⟨N, hN⟩ := hω
  refine ⟨N, fun n hn i ↦ ?_⟩
  apply edist_unitDyadicGrid_child_parent_le_of_adjacent_le
  intro k
  exact (hN (n + 1) (hn.trans (Nat.le_succ n)) k).le

end DyadicMultiscale

section DyadicAncestorChaining

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]





@[simp]
theorem unitDyadicAncestorIndex_succ
    (n r : ℕ) (i : Fin (2 ^ (n + (r + 1)) + 1)) :
    unitDyadicAncestorIndex n (r + 1) i =
      unitDyadicAncestorIndex n r (unitDyadicParentIndex (n + r) i) :=
  rfl



/-- Almost surely, every sufficiently fine base level admits all finite canonical ancestor
chains, with total increment bounded by the finite sum of dyadic thresholds along the chain. -/
theorem IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_ancestor_le_sum_threshold
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ᶠ n in Filter.atTop, ∀ r (i : Fin (2 ^ (n + r) + 1)),
      edist (X (unitDyadicGrid (n + r) i) ω)
          (X (unitDyadicGrid n (unitDyadicAncestorIndex n r i)) ω) ≤
        ∑ s ∈ Finset.range r, dyadicIncrementThreshold γ (n + s + 1) := by
  filter_upwards
    [IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_child_parent_le_threshold
      hX hγ hγq] with ω hω
  rw [Filter.eventually_atTop] at hω ⊢
  obtain ⟨N, hN⟩ := hω
  refine ⟨N, fun n hn r i ↦ ?_⟩
  apply edist_unitDyadicGrid_ancestor_le_sum_of_child_parent_le
  intro s _hs j
  exact hN (n + s) (hn.trans (Nat.le_add_right n s)) j

end DyadicAncestorChaining

section DyadicAncestorTail

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

/-- Every finite sum of thresholds above base level `n` is bounded by the exact infinite
tail beginning at level `n + 1`. -/
theorem sum_dyadicIncrementThreshold_ancestor_le_tail (γ : ℝ) (n r : ℕ) :
    ∑ s ∈ Finset.range r, dyadicIncrementThreshold γ (n + s + 1) ≤
      dyadicIncrementThreshold γ (n + 1) *
        (1 - dyadicIncrementThresholdRatio γ)⁻¹ := by
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    sum_dyadicIncrementThreshold_add_le γ (n + 1) r

/-- Almost surely, above every sufficiently fine base level, all finite canonical ancestor
chains are bounded uniformly in their depth and endpoint by the exact infinite threshold
tail. -/
theorem IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_ancestor_le_tail
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ r (i : Fin (2 ^ (n + r) + 1)),
      edist (X (unitDyadicGrid (n + r) i) ω)
          (X (unitDyadicGrid n (unitDyadicAncestorIndex n r i)) ω) ≤
        dyadicIncrementThreshold γ (n + 1) *
          (1 - dyadicIncrementThresholdRatio γ)⁻¹ := by
  filter_upwards
    [IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_ancestor_le_sum_threshold
      hX hγ hγq] with ω hω
  filter_upwards [hω] with n hn
  intro r i
  exact (hn r i).trans (sum_dyadicIncrementThreshold_ancestor_le_tail γ n r)
end DyadicAncestorTail
end MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dyadic floor approximation and the unit-interval continuous modification

This file merges the following former modules, one section each:

* `DyadicFloorApproximation`: Left dyadic approximations of unit-interval times
* `DyadicFloorPair`: Comparing two dyadic floor approximations
* `DyadicFloorSampleCauchy`: Cauchy control of dyadic floor samples
* `DyadicFloorDenseTime`: Dyadic floor samples at dyadic times
* `DyadicFloorSampleLimit`: Limits of dyadic floor samples
* `DyadicFloorLimitControl`: Uniform control of dyadic floor-sample limits
* `DyadicFloorLimitPath`: The canonical unit-interval dyadic-floor limit path
* `DyadicFloorConvergenceInMeasure`: Convergence in measure of dyadic floor samples
* `DyadicFloorUnitModification`: A continuous modification on the unit interval
-/




noncomputable section











/-- Passing from level `n + 1` to its canonical parent recovers the level-`n` left index. -/
theorem MarkovProcess.unitDyadicParentIndex_floorIndex (n : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    unitDyadicParentIndex n (unitDyadicFloorIndex (n + 1) t) =
      unitDyadicFloorIndex n t := by
  apply Fin.ext
  simp only [unitDyadicParentIndex_val, unitDyadicFloorIndex_val]
  have harg : (2 ^ (n + 1) : ℝ) * t.1 = ((2 ^ n : ℝ) * t.1) * 2 := by
    rw [pow_succ]
    ring
  rw [harg]
  exact Nat.mul_cast_floor_div_cancel (R := ℝ) (by norm_num : 2 ≠ 0)
    ((2 ^ n : ℝ) * t.1)






open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


noncomputable section












open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

/-- Iterating canonical parents of the level-`n + r` floor index recovers the level-`n`
floor index. -/
theorem MarkovProcess.unitDyadicAncestorIndex_floorIndex
    (n r : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    unitDyadicAncestorIndex n r (unitDyadicFloorIndex (n + r) t) =
      unitDyadicFloorIndex n t := by
  induction r with
  | zero => rfl
  | succ r ihr =>
      have hparent :
          unitDyadicParentIndex (n + r) (unitDyadicFloorIndex (n + (r + 1)) t) =
            unitDyadicFloorIndex (n + r) t := by
        simpa only [Nat.add_assoc] using! unitDyadicParentIndex_floorIndex (n + r) t
      rw [unitDyadicAncestorIndex_succ, hparent]
      exact ihr

/-- Almost surely, above every sufficiently fine base level, the floor samples at levels
`n + r` and `n` are bounded uniformly in the depth `r` and time `t` by the vanishing
ancestor tail. -/
theorem MarkovProcess.IsKolmogorovProcess.ae_eventually_edist_unitDyadicFloorValue_add_le_tail
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ r (t : Set.Icc (0 : ℝ) 1),
      edist (X (unitDyadicFloorValue (n + r) t) ω)
          (X (unitDyadicFloorValue n t) ω) ≤
        dyadicIncrementThreshold γ (n + 1) *
          (1 - dyadicIncrementThresholdRatio γ)⁻¹ := by
  filter_upwards
    [IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_ancestor_le_tail
      hX hγ hγq] with ω hω
  filter_upwards [hω] with n hn
  intro r t
  simpa only [unitDyadicFloorValue, unitDyadicAncestorIndex_floorIndex] using
    hn r (unitDyadicFloorIndex (n + r) t)


theorem solution
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ t : Set.Icc (0 : ℝ) 1,
      CauchySeq (fun n : ℕ ↦ X (unitDyadicFloorValue n t) ω) := by
  filter_upwards
    [IsKolmogorovProcess.ae_eventually_edist_unitDyadicFloorValue_add_le_tail
      hX hγ hγq] with ω hω
  rw [eventually_atTop] at hω
  obtain ⟨N₀, hN₀⟩ := hω
  intro t
  apply EMetric.cauchySeq_iff'.2
  intro ε hε
  have htail : ∀ᶠ n : ℕ in atTop,
      dyadicIncrementThreshold γ (n + 1) *
          (1 - dyadicIncrementThresholdRatio γ)⁻¹ < ε :=
    (tendsto_dyadicIncrementThreshold_ancestor_tail_zero hγ).eventually
      (gt_mem_nhds hε)
  rw [eventually_atTop] at htail
  obtain ⟨N₁, hN₁⟩ := htail
  let N := max N₀ N₁
  refine ⟨N, fun m hm ↦ ?_⟩
  let r := m - N
  have hNm : N + r = m := Nat.add_sub_of_le hm
  have hbound := hN₀ N (le_max_left N₀ N₁) r t
  have htailN := hN₁ N (le_max_right N₀ N₁)
  rw [hNm] at hbound
  exact hbound.trans_lt htailN
