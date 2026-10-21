-- Prove2me | solution 1 for LargeForkJoin.FluidLimit.lemma_4_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:12:20.482691+00:00
-- url     : https://prove2.me/submissions/6634ad7c-19a4-4012-8dfb-2d199229184b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LargeForkJoin_FluidLimit_Model
import Theorems.Thm_LargeForkJoin_FluidLimit_lemma_4_6
import Theorems.Thm_LargeForkJoin_FluidLimit_lemma_4_7
import Theorems.Thm_LargeForkJoin_FluidLimit_lemma_4_8

open MeasureTheory ProbabilityTheory Filter Topology

namespace FJLemma45Aux
open LargeForkJoin.FluidLimit

lemma measurable_maxQueueEmpty {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : ForkJoin Ω)
    (α β : ℝ) (N₀ : ℕ) (hM : IsModel P M α β N₀) (N n : ℕ) :
    Measurable (maxQueueEmpty M N n) := by
  have hX := hM.2.2.1
  have hY := hM.2.2.2.1
  have harr : ∀ k, Measurable (arr M N k) := by
    intro k
    unfold arr
    exact Finset.measurable_sum _ fun j hj => hX N j (Finset.mem_Icc.mp hj).1
  have hsrv : ∀ (i : Fin N) k, Measurable (srv M N i k) := by
    intro i k
    unfold srv
    exact Finset.measurable_sum _ fun j hj => hY N i j (Finset.mem_Icc.mp hj).1
  unfold maxQueueEmpty
  refine Measurable.iSup fun i => ?_
  unfold queueEmpty
  refine Finset.measurable_range_sup'' fun k _ => ?_
  exact (((harr n).sub (harr k)).sub ((hsrv i n).sub (hsrv i k)))

end FJLemma45Aux

open LargeForkJoin.FluidLimit FJLemma45Aux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ForkJoin Ω) (α β : ℝ) (N₀ : ℕ) (hM : IsModel P M α β N₀) (t : ℝ) (ht : 0 < t) :
    ∀ ε > 0, Tendsto (fun N : ℕ => P {ω | ε <
      |maxQueueEmpty M N (tau N t) ω / scale N - fluidEmpty α β t|}) atTop (𝓝 0) := by
  intro ε hε
  set X : ℕ → Ω → ℝ := fun N ω => maxQueueEmpty M N (tau N t) ω / scale N with hX
  have hXm : ∀ N, Measurable (X N) := fun N =>
    (measurable_maxQueueEmpty P M α β N₀ hM N (tau N t)).div_const _
  -- upper tail
  have hup : Tendsto (fun N => P {ω | fluidEmpty α β t + ε < X N ω}) atTop (𝓝 0) := by
    by_cases hlt : t < α / (2 * β ^ 2)
    · have := lemma_4_6 P M α β N₀ hM ε t hε ht.le hlt
      simp only [fluidEmpty, if_pos hlt]
      exact this
    · have := lemma_4_7 P M α β N₀ hM ε t hε (not_lt.mp hlt)
      simp only [fluidEmpty, if_neg hlt]
      exact this
  -- lower tail
  have hlo : Tendsto (fun N => P {ω | X N ω < fluidEmpty α β t - ε}) atTop (𝓝 0) := by
    have h8 := lemma_4_8 P M α β N₀ hM ε t hε ht.le
    have hc : ∀ N, P {ω | X N ω < fluidEmpty α β t - ε} =
        1 - P {ω | fluidEmpty α β t - ε ≤ X N ω} := by
      intro N
      have hms : MeasurableSet {ω | fluidEmpty α β t - ε ≤ X N ω} :=
        measurableSet_le measurable_const (hXm N)
      rw [← prob_compl_eq_one_sub hms]
      congr 1
      ext ω
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
    simp only [hc]
    have := (ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ENNReal))) h8
      (Or.inl ENNReal.one_ne_top))
    simpa using this
  have hsum := hup.add hlo
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) (fun N => le_trans (measure_mono ?_) (measure_union_le _ _))
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  rcases lt_abs.mp hω with h | h
  · exact Or.inl (show fluidEmpty α β t + ε < X N ω by simp only [hX]; linarith)
  · exact Or.inr (show X N ω < fluidEmpty α β t - ε by simp only [hX]; linarith)
