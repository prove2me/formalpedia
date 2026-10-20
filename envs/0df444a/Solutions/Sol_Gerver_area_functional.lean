-- Prove2me | solution 1 for Gerver.area_functional
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T23:21:42.559377+00:00
-- url     : https://prove2.me/submissions/d8188078-cdd8-4506-86c6-6520a091903e

import Mathlib
import Definitions.Def_Gerver_arena
import Definitions.Def_Gerver_monotone
import Definitions.Def_Gerver_sofa

open MeasureTheory

namespace Gerver

lemma af_set (x : ℝ → ℝ × ℝ) (ω : ℝ) :
    sofaOfPath x ω = capOf x ω \ nicheOf x ω := by
  ext p
  simp only [sofaOfPath, capOf, nicheOf, Set.mem_inter_iff, Set.mem_iInter, Set.mem_sdiff,
    Set.mem_iUnion, not_and, not_exists]
  constructor
  · rintro ⟨hp, h⟩
    exact ⟨⟨hp, fun t ht => (h t ht).1⟩, fun _ t ht => (h t ht).2⟩
  · rintro ⟨⟨hp, h1⟩, h2⟩
    have hf : p ∈ fan ω := ⟨hp.1.1, hp.2.1⟩
    exact ⟨hp, fun t ht => ⟨h1 t ht, h2 hf t ht⟩⟩

lemma af_open (x : ℝ → ℝ × ℝ) (ω : ℝ) : IsOpen (⋃ t ∈ Set.Icc 0 ω, Qminus x t) := by
  refine isOpen_biUnion fun t _ => ?_
  unfold Qminus dot
  exact (isOpen_lt (by fun_prop : Continuous fun p : ℝ × ℝ =>
      (p - x t).1 * (u t).1 + (p - x t).2 * (u t).2) continuous_const).inter
    (isOpen_lt (by fun_prop : Continuous fun p : ℝ × ℝ =>
      (p - x t).1 * (v t).1 + (p - x t).2 * (v t).2) continuous_const)

lemma af_closed (ω : ℝ) : IsClosed (fan ω) := by
  unfold fan dot
  exact (isClosed_le continuous_const (by fun_prop : Continuous fun p : ℝ × ℝ => p.2)).inter
    (isClosed_le continuous_const (by fun_prop : Continuous fun p : ℝ × ℝ =>
      p.1 * (u ω).1 + p.2 * (u ω).2))

lemma af_bdd (x : ℝ → ℝ × ℝ) (ω : ℝ) (hω : 0 ≤ ω) :
    ∃ a b : ℝ, capOf x ω ⊆ Set.Icc a b ×ˢ Set.Icc 0 1 := by
  have h0 : (0:ℝ) ∈ Set.Icc 0 ω := ⟨le_rfl, hω⟩
  rcases lt_or_ge ω (Real.pi / 2) with hlt | hge
  · have hc : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hlt⟩
    refine ⟨-1 / Real.cos ω, (x 0).1 + 1, ?_⟩
    intro p hp
    simp only [capOf, Set.mem_inter_iff, Set.mem_iInter] at hp
    obtain ⟨⟨⟨hy0, hy1⟩, hv0, hv1⟩, hq⟩ := hp
    have q0 := (hq 0 h0).1
    simp only [dot, u, v, Real.cos_zero, Real.sin_zero, Prod.fst_sub, Prod.snd_sub,
      Prod.fst_add, Prod.snd_add] at q0 hv0
    have hs : Real.sin ω ≤ 1 := Real.sin_le_one ω
    have hs' : 0 ≤ Real.sin ω := Real.sin_nonneg_of_nonneg_of_le_pi hω (by linarith)
    refine ⟨⟨?_, by linarith⟩, hy0, hy1⟩
    rw [div_le_iff₀ hc]
    nlinarith
  · have h2 : Real.pi / 2 ∈ Set.Icc 0 ω := ⟨by linarith [Real.pi_pos], hge⟩
    refine ⟨(x (Real.pi / 2)).1 - 1, (x 0).1 + 1, ?_⟩
    intro p hp
    simp only [capOf, Set.mem_inter_iff, Set.mem_iInter] at hp
    obtain ⟨⟨⟨hy0, hy1⟩, _⟩, hq⟩ := hp
    have q0 := (hq 0 h0).1
    have q2 := (hq _ h2).2
    simp only [dot, u, v, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two,
      Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at q0 q2
    exact ⟨⟨by linarith, by linarith⟩, hy0, hy1⟩

end Gerver

open Gerver in
theorem solution (x : ℝ → ℝ × ℝ) (ω : ℝ)
    (hsub : nicheOf x ω ⊆ capOf x ω) :
    area (sofaOfPath x ω) = area (capOf x ω) - area (nicheOf x ω) := by
  have hmeas : MeasurableSet (nicheOf x ω) :=
    ((af_closed ω).measurableSet).inter (af_open x ω).measurableSet
  unfold area
  rw [af_set]
  rcases lt_or_ge ω 0 with hneg | hω
  · have he : nicheOf x ω = ∅ := by
      simp [nicheOf, Set.Icc_eq_empty_of_lt hneg]
    simp [he]
  · obtain ⟨a, b, hab⟩ := af_bdd x ω hω
    have hfin : vol2 (capOf x ω) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (measure_mono hab)
      rw [vol2, Measure.prod_prod]
      simp [Real.volume_Icc, ENNReal.mul_eq_top]
    rw [measure_diff hsub hmeas.nullMeasurableSet (ne_top_of_le_ne_top hfin (measure_mono hsub)),
      ENNReal.toReal_sub_of_le (measure_mono hsub) hfin]
