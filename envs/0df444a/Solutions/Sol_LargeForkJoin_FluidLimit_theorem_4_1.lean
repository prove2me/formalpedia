-- Prove2me | solution 1 for LargeForkJoin.FluidLimit.theorem_4_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:01:48.74471+00:00
-- url     : https://prove2.me/submissions/83d75662-0126-4f15-b80e-936a7e78ce6a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LargeForkJoin_FluidLimit_Model
import Theorems.Thm_LargeForkJoin_FluidLimit_lemma_4_4
import Theorems.Thm_LargeForkJoin_FluidLimit_lemma_4_5
import Theorems.Thm_LargeForkJoin_FluidLimit_lemma_4_9

open MeasureTheory ProbabilityTheory Filter Topology

namespace FJThm41Aux
open LargeForkJoin.FluidLimit

lemma maxQueue_eq {Ω : Type*} (M : ForkJoin Ω) (N n : ℕ) (ω : Ω) (hN : 0 < N) :
    maxQueue M N n ω = max (maxQueueEmpty M N n ω) (maxStartPart M N n ω) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have b1 : BddAbove (Set.range fun i : Fin N => queueEmpty M N i n ω) :=
    (Set.finite_range _).bddAbove
  have b2 : BddAbove (Set.range fun i : Fin N =>
      arr M N n ω - srv M N i n ω + initLen M N i ω) := (Set.finite_range _).bddAbove
  unfold maxQueue maxQueueEmpty maxStartPart
  apply le_antisymm
  · refine ciSup_le fun i => ?_
    unfold queueLen
    refine max_le_max (le_ciSup b1 i) ?_
    refine le_trans (le_of_eq (by ring)) (le_ciSup b2 i)
  · refine max_le (ciSup_le fun i => ?_) (ciSup_le fun i => ?_)
    · have b3 : BddAbove (Set.range fun i : Fin N => queueLen M N i n ω) :=
        (Set.finite_range _).bddAbove
      exact le_trans (le_max_left _ _) (le_ciSup b3 i)
    · have b3 : BddAbove (Set.range fun i : Fin N => queueLen M N i n ω) :=
        (Set.finite_range _).bddAbove
      refine le_trans ?_ (le_ciSup b3 i)
      unfold queueLen
      exact le_trans (le_of_eq (by ring)) (le_max_right _ _)

lemma max_conv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y Z : ℕ → Ω → ℝ) (k l : ℝ)
    (hZ : ∀ᶠ N in atTop, ∀ ω, Z N ω = max (X N ω) (Y N ω))
    (hX : ∀ ε > 0, Tendsto (fun N => P {ω | ε < |X N ω - k|}) atTop (𝓝 0))
    (hY : ∀ ε > 0, Tendsto (fun N => P {ω | ε < |Y N ω - l|}) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun N => P {ω | ε < |Z N ω - max k l|}) atTop (𝓝 0) := by
  intro ε hε
  have hsum := (hX ε hε).add (hY ε hε)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hZ] with N hN
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hlt
  simp only [Set.mem_ofPred_eq, hN ω] at hlt
  have key : |max (X N ω) (Y N ω) - max k l| ≤ max |X N ω - k| |Y N ω - l| :=
    abs_max_sub_max_le_max _ _ _ _
  by_cases h1 : ε < |X N ω - k|
  · exact Or.inl h1
  · refine Or.inr ?_
    push Not at h1
    show ε < |Y N ω - l|
    rcases le_total |X N ω - k| |Y N ω - l| with h | h
    · rw [max_eq_right h] at key; linarith
    · rw [max_eq_left h] at key; linarith

end FJThm41Aux

open LargeForkJoin.FluidLimit FJThm41Aux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ForkJoin Ω) (α β qInit : ℝ) (N₀ : ℕ)
    (hM : IsModel P M α β N₀) (h23 : Assumption23 P M qInit) (t : ℝ) (ht : 0 < t) :
    (Assumption24 P M → ∀ ε > 0, Tendsto (fun N : ℕ => P {ω | ε <
      |maxQueue M N (tau N t) ω / scale N - fluid α β (gFinite α qInit) t|}) atTop (𝓝 0)) ∧
    (∀ h : ℝ → ℝ, Assumption25 P M h → ∀ ε > 0, Tendsto (fun N : ℕ => P {ω | ε <
      |maxQueue M N (tau N t) ω / scale N - fluid α β (gGumbel α h qInit) t|}) atTop (𝓝 0)) := by
  have hZ : ∀ᶠ N in atTop, ∀ ω, maxQueue M N (tau N t) ω / scale N =
      max (maxQueueEmpty M N (tau N t) ω / scale N) (maxStartPart M N (tau N t) ω / scale N) := by
    filter_upwards [eventually_ge_atTop 1] with N hN ω
    rw [maxQueue_eq M N _ ω hN]
    have : 0 ≤ scale N := by unfold scale; have := Real.log_natCast_nonneg N; positivity
    exact (max_div_div_right this _ _).symm
  have hE := lemma_4_5 P M α β N₀ hM t ht
  have h44 := lemma_4_4 P M α β qInit N₀ hM h23 t ht
  constructor
  · intro h24
    have hS := lemma_4_9 P M α β N₀ hM t (gFinite α qInit t) ht (h44.1 h24)
    exact max_conv P _ _ _ _ _ hZ hE hS
  · intro h h25
    have hS := lemma_4_9 P M α β N₀ hM t (gGumbel α h qInit t) ht (h44.2 h h25)
    exact max_conv P _ _ _ _ _ hZ hE hS
