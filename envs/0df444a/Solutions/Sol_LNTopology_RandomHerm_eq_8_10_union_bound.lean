-- Prove2me | solution 1 for LNTopology.RandomHerm.eq_8_10_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T02:55:36.456762+00:00
-- url     : https://prove2.me/submissions/8ea44dea-33f2-4701-b4aa-80bb597e00ab

import Mathlib
import Definitions.Def_LNTopology_Local_Model
import Definitions.Def_LNTopology_Hermetic_Model
import Definitions.Def_LNTopology_RandomHerm_ChannelCost
import Definitions.Def_LNTopology_RandomHerm_Hermetization
import Theorems.Thm_LNTopology_RandomHerm_lemma_B_1

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

lemma c_meas {c : ℝ → ℝ} (hc : IsChannelCost c) : Measurable c := by
  have hmono : Monotone (fun x => c (max x 0)) := fun x y hxy =>
    c_le hc (le_max_right _ _) (max_le_max hxy le_rfl)
  have : c = (fun x => c (max x 0)) ∘ (fun x => |x|) := by
    funext x; simp [max_eq_left (abs_nonneg x), c_abs hc]
  rw [this]; exact hmono.measurable.comp continuous_abs.measurable

end LNRHHelp

open LNTopology.RandomHerm LNRHHelp

theorem solution {V : Type} [Fintype V] [DecidableEq V] (E : SimpleGraph V)
    [DecidableRel E.Adj] {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : Ω → V → V → ℝ) (c g : ℝ → ℝ) (hc : LNTopology.Local.IsChannelCost c) (hg : LNTopology.Hermetic.SAPlus c g)
    (hLN : ∀ ω, LNTopology.Local.IsLN (Λ ω)) (hE : ∀ ω i j, Λ ω i j ≠ 0 ↔ E.Adj i j)
    (hchan : ∃ u v, E.Adj u v) :
    1 - ∑ i ∈ Finset.univ.filter (fun i => 0 < E.degree i),
        (P {ω | g (E.degree i) ≤
          2 * c (maxChanOn (Λ ω) Finset.univ i) / c (minChanOn (Λ ω) Finset.univ i)}).toReal
      ≤ (P {ω | IsHermetizableLN c (Λ ω)}).toReal := by
  set U := Finset.univ.filter (fun i => 0 < E.degree i) with hU
  have hnbr : ∀ ω i (W : Finset V), (∀ j, 0 < E.degree j → j ∈ W) →
      chanNbrs (Λ ω) W i = E.neighborFinset i := by
    intro ω i W hW; ext j
    simp only [chanNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset, hE]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨hW j ((E.degree_pos_iff_exists_adj j).2 ⟨i, h.symm⟩), h⟩
  have hnbrU : ∀ ω i, chanNbrs (Λ ω) U i = chanNbrs (Λ ω) Finset.univ i := by
    intro ω i
    rw [hnbr ω i U (fun j hj => by simpa [hU] using hj),
      hnbr ω i Finset.univ (fun j _ => Finset.mem_univ j)]
  have hmaxU : ∀ ω i, maxChanOn (Λ ω) U i = maxChanOn (Λ ω) Finset.univ i := by
    intro ω i; simp only [maxChanOn, hnbrU]
  have hminU : ∀ ω i, minChanOn (Λ ω) U i = minChanOn (Λ ω) Finset.univ i := by
    intro ω i; simp only [minChanOn, hnbrU]
  have hdegU : ∀ ω i, degOn (Λ ω) U i = E.degree i := by
    intro ω i
    simp [degOn, hnbrU, hnbr ω i Finset.univ (fun j _ => Finset.mem_univ j),
      SimpleGraph.card_neighborFinset_eq_degree]
  let F : V → Set Ω := fun i =>
    {ω | g (E.degree i) ≤
      2 * c (maxChanOn (Λ ω) Finset.univ i) / c (minChanOn (Λ ω) Finset.univ i)}
  have hcompl : {ω | IsHermetizableLN c (Λ ω)}ᶜ ⊆ ⋃ i ∈ U, F i := by
    intro ω hω
    by_contra hcon
    apply hω
    refine ⟨U, lemma_B_1 c g (Λ ω) U hc hg (hLN ω) ?_ ?_ ?_⟩
    · obtain ⟨u, v, huv⟩ := hchan
      have hu : 0 < E.degree u := (E.degree_pos_iff_exists_adj u).2 ⟨v, huv⟩
      exact ⟨u, by simpa only [hU, Finset.mem_filter, Finset.mem_univ, true_and] using hu⟩
    · intro i hi; rw [hdegU]; simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hi
    · intro i hi
      simp only [Set.mem_iUnion, not_exists] at hcon
      have := hcon i hi
      simp only [F, Set.mem_setOf_eq, not_le] at this
      rw [hdegU, hmaxU, hminU]; exact this
  have h1 : 1 ≤ (P {ω | IsHermetizableLN c (Λ ω)}).toReal
      + (P {ω | IsHermetizableLN c (Λ ω)}ᶜ).toReal := by
    have hle : (1 : ENNReal) ≤ P {ω | IsHermetizableLN c (Λ ω)}
        + P {ω | IsHermetizableLN c (Λ ω)}ᶜ := by
      rw [← measure_univ (μ := P), ← Set.union_compl_self {ω | IsHermetizableLN c (Λ ω)}]
      exact measure_union_le _ _
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    have := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hle
    simpa using this
  have h2 : (P {ω | IsHermetizableLN c (Λ ω)}ᶜ).toReal ≤ ∑ i ∈ U, (P (F i)).toReal := by
    rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]
    apply ENNReal.toReal_mono
    · exact ENNReal.sum_ne_top.2 (fun i _ => measure_ne_top _ _)
    · exact (measure_mono hcompl).trans (measure_biUnion_finset_le U F)
  have h3 : ∑ i ∈ U, (P (F i)).toReal = ∑ i ∈ Finset.univ.filter (fun i => 0 < E.degree i),
        (P {ω | g (E.degree i) ≤
          2 * c (maxChanOn (Λ ω) Finset.univ i) / c (minChanOn (Λ ω) Finset.univ i)}).toReal := rfl
  linarith
