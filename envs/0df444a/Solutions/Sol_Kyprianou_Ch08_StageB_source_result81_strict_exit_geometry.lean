-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_strict_exit_geometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T13:38:00.544594+00:00
-- url     : https://prove2.me/submissions/489a3848-575c-4ea7-99fe-666b4f14b279

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.LeftRightNhds
open Set Filter Topology MeasureTheory ProbabilityTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem closed_value_at_finite_strict_lower_clock
    (f : ℝ≥0 → ℝ) (t : ℝ≥0) (hright : ContinuousWithinAt f (Ici t) t)
    (ht : tauMinus (fun s (_ : Unit) => f s) 0 () = (t : WithTop ℝ≥0)) :
    f t ≤ 0 := by
  by_contra! hpositive
  have hnear : f ⁻¹' Ioi (0 : ℝ) ∈ nhdsWithin t (Ici t) :=
    hright (Ioi_mem_nhds hpositive)
  obtain ⟨b, hb, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hnear
  let S : Set (WithTop ℝ≥0) :=
    {u | ∃ s : ℝ≥0, 0 < s ∧ (s : WithTop ℝ≥0) = u ∧ f s < 0}
  change sInf S = (t : WithTop ℝ≥0) at ht
  have hlt : sInf S < (b : WithTop ℝ≥0) := by
    rw [ht, WithTop.coe_lt_coe]
    exact hb
  have hwitness : ∃ u ∈ S, u < (b : WithTop ℝ≥0) := by
    by_contra! hall
    exact (not_le_of_gt hlt) (le_sInf hall)
  obtain ⟨u, ⟨s, hspos, rfl, hsnegative⟩, hsupper⟩ := hwitness
  have hs_mem : (s : WithTop ℝ≥0) ∈ S := ⟨s, hspos, rfl, hsnegative⟩
  have hts : t ≤ s := by
    apply WithTop.coe_le_coe.mp
    rw [← ht]
    exact sInf_le hs_mem
  have hfs : 0 < f s := hsub ⟨hts, WithTop.coe_lt_coe.mp hsupper⟩
  exact (not_lt_of_ge hfs.le) hsnegative

private theorem closed_value_at_finite_strict_upper_clock
    (f : ℝ≥0 → ℝ) (a : ℝ) (t : ℝ≥0) (hright : ContinuousWithinAt f (Ici t) t)
    (ht : tauPlus (fun s (_ : Unit) => f s) a () = (t : WithTop ℝ≥0)) :
    a ≤ f t := by
  have h := closed_value_at_finite_strict_lower_clock (fun s => a - f s) t
    (continuous_const.continuousWithinAt.sub hright)
    (by simpa only [tauPlus, tauMinus, sub_lt_zero] using ht)
  linarith

private theorem finite_strict_upper_clock_value
    (f : ℝ≥0 → ℝ) (a : ℝ) (t : ℝ≥0)
    (hstart : f 0 ≤ a) (hcad : IsCadlag f)
    (hjumps : ∀ (s : ℝ≥0) (l : ℝ), 0 < s →
      Tendsto f (nhdsWithin s (Iio s)) (nhds l) → f s ≤ l)
    (ht : tauPlus (fun s (_ : Unit) => f s) a () = (t : WithTop ℝ≥0)) :
    f t = a := by
  refine le_antisymm ?_ (closed_value_at_finite_strict_upper_clock f a t (hcad t).1 ht)
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ t by positivity) with hzero | hpos
  · simpa [← hzero] using hstart
  · obtain ⟨l, hl⟩ := (hcad t).2
    haveI : (nhdsWithin t (Iio t)).NeBot := nhdsWithin_Iio_self_neBot' ⟨0, hpos⟩
    refine (hjumps t l hpos hl).trans (le_of_tendsto hl ?_)
    filter_upwards [self_mem_nhdsWithin] with s hs
    by_cases hspos : 0 < s
    · by_contra! hcross
      have hlt : (t : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0) := by
        rw [← ht]
        exact sInf_le ⟨s, hspos, rfl, hcross⟩
      exact (not_le_of_gt hs) (WithTop.coe_le_coe.mp hlt)
    · simpa [le_antisymm (le_of_not_gt hspos) (by positivity)] using hstart

theorem solution
    (f : ℝ≥0 → ℝ) (a : ℝ) (ha : 0 < a) (hstart : f 0 ≤ a)
    (hcad : IsCadlag f)
    (hjumps : ∀ (s : ℝ≥0) (l : ℝ), 0 < s →
      Tendsto f (nhdsWithin s (Iio s)) (nhds l) → f s ≤ l) :
    let L := tauMinus (fun s (_ : Unit) => f s) 0 ()
    let U := tauPlus (fun s (_ : Unit) => f s) a ()
    (∀ t : ℝ≥0, U = (t : WithTop ℝ≥0) → f t = a) ∧
      (L = U → L = ⊤) := by
  intro L U
  refine ⟨fun t ht => finite_strict_upper_clock_value f a t hstart hcad hjumps ht, ?_⟩
  intro heq
  by_contra ht
  obtain ⟨t, htL⟩ := WithTop.ne_top_iff_exists.mp ht
  have h0 := closed_value_at_finite_strict_lower_clock f t (hcad t).1 htL.symm
  have h1 := closed_value_at_finite_strict_upper_clock f a t (hcad t).1
    (heq.symm.trans htL.symm)
  linarith
