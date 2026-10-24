-- Prove2me | solution 1 for LNTopology.RandomHerm.eq_12_13_max_tail
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T02:57:43.785494+00:00
-- url     : https://prove2.me/submissions/f65ac4a2-7b01-447f-b5e2-89947b58bc79

import Mathlib
import Definitions.Def_LNTopology_Local_Model
import Definitions.Def_LNTopology_Hermetic_Model
import Definitions.Def_LNTopology_RandomHerm_ChannelCost
import Definitions.Def_LNTopology_RandomHerm_Hermetization

open MeasureTheory

namespace LNRHHelp
open LNTopology.Local LNTopology.Hermetic LNTopology.RandomHerm

lemma c_le {c : ℝ → ℝ} (hc : IsChannelCost c) {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) :
    c y ≤ c x := by
  rcases hxy.lt_or_eq with h | h
  · exact (hc.mono x y hy h).le
  · rw [h]

lemma c_abs {c : ℝ → ℝ} (hc : IsChannelCost c) (x : ℝ) : c |x| = c x := by
  rcases abs_choice x with h | h <;> rw [h]
  exact hc.symm x

lemma c_pos {c : ℝ → ℝ} (hc : IsChannelCost c) {x : ℝ} (hx : 0 < x) : 0 < c x := by
  have := hc.mono x 0 le_rfl hx
  rwa [hc.zero] at this

end LNRHHelp

open LNTopology.RandomHerm LNRHHelp

lemma tail_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℝ) (a b x : ℝ)
    (hx : 0 < x) (h : ∀ y : ℝ, 0 < y → P {ω | y < f ω} < ENNReal.ofReal (b * y ^ (-a))) :
    P {ω | x ≤ f ω} ≤ ENNReal.ofReal (b * x ^ (-a)) := by
  have hcont : ContinuousAt (fun y : ℝ => ENNReal.ofReal (b * y ^ (-a))) x :=
    ENNReal.continuous_ofReal.continuousAt.comp
      (continuousAt_const.mul (Real.continuousAt_rpow_const x (-a) (Or.inl hx.ne')))
  have ht : Filter.Tendsto (fun y : ℝ => ENNReal.ofReal (b * y ^ (-a))) (nhdsWithin x (Set.Iio x))
      (nhds (ENNReal.ofReal (b * x ^ (-a)))) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT (half_lt_self hx)] with y hy
  have hy0 : 0 < y := lt_trans (half_pos hx) hy.1
  refine le_trans (measure_mono ?_) (h y hy0).le
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  exact lt_of_lt_of_le hy.2 hω

theorem solution {V : Type} [Fintype V] [DecidableEq V] (E : SimpleGraph V)
    [DecidableRel E.Adj] {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : Ω → V → V → ℝ) (c : ℝ → ℝ) (hc : LNTopology.Local.IsChannelCost c)
    (hE : ∀ ω i j, Λ ω i j ≠ 0 ↔ E.Adj i j) (a b : ℝ) (_ha : 1 < a) (hb : 0 < b)
    (hi_tail : ∀ i j, E.Adj i j → ∀ x : ℝ, 0 < x →
      P {ω | x < c (Λ ω i j)} < ENNReal.ofReal (b * x ^ (-a)))
    (i : V) (x : ℝ) (hx : 0 < x) :
    P {ω | x ≤ c (maxChanOn (Λ ω) Finset.univ i)}
      ≤ ENNReal.ofReal ((E.degree i : ℝ) * b * x ^ (-a)) := by
  have hnbr : ∀ ω, chanNbrs (Λ ω) Finset.univ i = E.neighborFinset i := by
    intro ω; ext j
    simp [chanNbrs, hE]
  have hsub : {ω | x ≤ c (maxChanOn (Λ ω) Finset.univ i)} ⊆
      ⋃ j ∈ E.neighborFinset i, {ω | x ≤ c (Λ ω i j)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    by_cases hne : (chanNbrs (Λ ω) Finset.univ i).Nonempty
    · obtain ⟨j1, hj1, h1⟩ := Finset.exists_mem_eq_sup' hne (fun j => |Λ ω i j|)
      have hmax : maxChanOn (Λ ω) Finset.univ i = |Λ ω i j1| := by
        simp only [maxChanOn, dif_pos hne]; exact h1
      rw [hmax, c_abs hc] at hω
      rw [hnbr] at hj1
      simp only [Set.mem_iUnion]
      exact ⟨j1, hj1, hω⟩
    · have hmax : maxChanOn (Λ ω) Finset.univ i = 0 := by
        simp only [maxChanOn, dif_neg hne]
      rw [hmax, hc.zero] at hω
      exact absurd hω (not_le.2 hx)
  have hb' : 0 ≤ b * x ^ (-a) := mul_nonneg hb.le (Real.rpow_nonneg hx.le _)
  calc P {ω | x ≤ c (maxChanOn (Λ ω) Finset.univ i)}
      ≤ P (⋃ j ∈ E.neighborFinset i, {ω | x ≤ c (Λ ω i j)}) := measure_mono hsub
    _ ≤ ∑ j ∈ E.neighborFinset i, P {ω | x ≤ c (Λ ω i j)} := measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ E.neighborFinset i, ENNReal.ofReal (b * x ^ (-a)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact tail_le P (fun ω => c (Λ ω i j)) a b x hx
          (hi_tail i j ((SimpleGraph.mem_neighborFinset E i j).1 hj))
    _ = ENNReal.ofReal ((E.degree i : ℝ) * b * x ^ (-a)) := by
        rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, mul_assoc,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
