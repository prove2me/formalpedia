-- Prove2me | solution 1 for LevyStochCalc.Probability.exists_one_le_measure_singleton
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:12:03.775969+00:00
-- url     : https://prove2.me/submissions/d86d71c7-4add-4988-b421-ab8badff8654

import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F000
import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Integer-valued finite measures

A measure is integer-valued when every measurable set carries a natural mass. On a measurable
space with a countable separating family such a measure, if finite, is a finite sum of Dirac
masses: a binary search along the separating family isolates a point of mass at least one, and
removing it lowers the total mass by at least one, so the recursion terminates.

Integrality on a generating π-system already gives integrality everywhere, since the sets of
natural mass form a Dynkin system as soon as the ambient measure is finite.
-/

namespace LevyStochCalc.Probability

open MeasureTheory Filter Set
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α]

section PiSystem

end PiSystem

section Atom

variable [MeasurableSpace.CountablySeparated α]



theorem _root_.solution (μ : Measure α) [IsFiniteMeasure μ]
    (hint : IsIntegerValued μ) (hpos : μ Set.univ ≠ 0) : ∃ x : α, 1 ≤ μ {x} := by
  classical
  obtain ⟨S, hSm, hsep⟩ := exists_seq_separating α MeasurableSet.empty Set.univ
  have one_le : ∀ B, MeasurableSet B → μ B ≠ 0 → 1 ≤ μ B := by
    intro B hB h0
    obtain ⟨n, hn⟩ := hint B hB
    rw [hn] at h0 ⊢
    have : n ≠ 0 := by rintro rfl; simp at h0
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have key : ∀ B s, MeasurableSet B → MeasurableSet s → 1 ≤ μ B →
      ¬ 1 ≤ μ (B ∩ s) → 1 ≤ μ (B \ s) := by
    intro B s hB hs h1 h2
    refine one_le _ (hB.diff hs) fun h0 => ?_
    have h3 : μ (B ∩ s) = 0 := by
      by_contra hne; exact h2 (one_le _ (hB.inter hs) hne)
    have := measure_inter_add_diff B hs (μ := μ)
    rw [h3, h0, add_zero] at this
    rw [← this] at h1
    simp at h1
  let T := {B : Set α // MeasurableSet B ∧ 1 ≤ μ B}
  let step : ℕ → T → T := fun n c =>
    if h : 1 ≤ μ (c.1 ∩ S n) then ⟨c.1 ∩ S n, c.2.1.inter (hSm n), h⟩
    else ⟨c.1 \ S n, c.2.1.diff (hSm n), key _ _ c.2.1 (hSm n) c.2.2 h⟩
  let C : ℕ → T := fun n => Nat.rec ⟨Set.univ, MeasurableSet.univ, one_le _ MeasurableSet.univ hpos⟩
    (fun k c => step k c) n
  have hCs : ∀ n, (C (n + 1)).1 = (step n (C n)).1 := fun n => rfl
  have hsub : ∀ n, (C (n + 1)).1 ⊆ (C n).1 := by
    intro n
    rw [hCs]
    simp only [step]
    split_ifs
    · exact Set.inter_subset_left
    · exact Set.diff_subset
  have hanti : Antitone fun n => (C n).1 := antitone_nat_of_succ_le hsub
  have hmeasI : μ (⋂ n, (C n).1) = ⨅ n, μ (C n).1 :=
    hanti.measure_iInter (fun n => (C n).2.1.nullMeasurableSet) ⟨0, measure_ne_top _ _⟩
  have hge : 1 ≤ μ (⋂ n, (C n).1) := by
    rw [hmeasI]; exact le_iInf fun n => (C n).2.2
  have hne : (⋂ n, (C n).1).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, measure_empty] at hge
    exact absurd hge (by simp)
  obtain ⟨x, hx⟩ := hne
  refine ⟨x, hge.trans (measure_mono fun y hy => ?_)⟩
  rw [Set.mem_singleton_iff]
  refine hsep y (Set.mem_univ _) x (Set.mem_univ _) fun n => ?_
  have hy1 := Set.mem_iInter.1 hy (n + 1)
  have hx1 := Set.mem_iInter.1 hx (n + 1)
  rw [hCs] at hy1 hx1
  simp only [step] at hy1 hx1
  split_ifs at hy1 hx1
  · exact ⟨fun _ => hx1.2, fun _ => hy1.2⟩
  · exact ⟨fun h => absurd h hy1.2, fun h => absurd h hx1.2⟩
