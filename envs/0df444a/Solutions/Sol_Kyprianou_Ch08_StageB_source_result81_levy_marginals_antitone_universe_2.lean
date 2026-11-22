-- Prove2me | solution 2 for Kyprianou.Ch08.StageB.source_result81_levy_marginals_antitone_universe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T21:09:09.270525+00:00
-- url     : https://prove2.me/submissions/f70e139b-0628-487b-96e9-7c5f869e5788

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Topology.Sequences
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem dense_right_sequence (K : Set ℝ≥0) (hK : Dense K) (t : ℝ≥0) :
    ∃ u : ℕ → K, Tendsto (fun n => (u n : ℝ≥0)) atTop (nhdsWithin t (Ici t)) := by
  have ht : t ∈ closure (Ioi t) := by
    simpa only [closure_Ioi, mem_Ici] using (le_rfl : t ≤ t)
  have hnear : t ∈ closure (K ∩ Ioi t) := by
    rw [mem_closure_iff] at ht ⊢
    intro U hU htU
    obtain ⟨a, haU, hat⟩ := ht U hU htU
    obtain ⟨z, hz, hzK⟩ := dense_iff_inter_open.mp hK (U ∩ Ioi t)
      (hU.inter isOpen_Ioi) ⟨a, haU, hat⟩
    exact ⟨z, hz.1, hzK, hz.2⟩
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp hnear
  refine ⟨fun n => ⟨v n, (hv n).1⟩, tendsto_nhdsWithin_iff.mpr ⟨hlim, ?_⟩⟩
  refine Eventually.of_forall fun n => ?_
  simpa only [mem_Ici] using (show t ≤ v n from (hv n).2.le)

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (h : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A.X t ω ≤ 0) :
    ∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => A.X t ω) := by
  obtain ⟨K, hKcount, hKdense⟩ := TopologicalSpace.exists_countable_dense (α := ℝ≥0)
  letI : Countable K := hKcount.to_subtype
  have hpair (s t : K) : ∀ᵐ ω ∂P, (s : ℝ≥0) ≤ t → A.X t ω ≤ A.X s ω := by
    by_cases hst : (s : ℝ≥0) ≤ t
    · have hsnd : P ((A.X ((t : ℝ≥0) - s)) ⁻¹' Ioi 0) = 0 := by
        simpa only [ae_iff, not_le, Set.preimage, mem_Ioi] using
          h ((t : ℝ≥0) - s)
      have hfst := ((A.stationaryIncrements s t hst).measure_mem_eq
        (s := Ioi (0 : ℝ)) measurableSet_Ioi).trans hsnd
      have hle : ∀ᵐ ω ∂P, A.X t ω ≤ A.X s ω := by
        rw [ae_iff]
        simpa only [Set.preimage, mem_Ioi, sub_pos, not_le] using hfst
      exact hle.mono fun _ hω _ => hω
    · exact Eventually.of_forall fun _ hle => (hst hle).elim
  have hcount : ∀ᵐ ω ∂P, ∀ s t : K, (s : ℝ≥0) ≤ t → A.X t ω ≤ A.X s ω :=
    ae_all_iff.mpr fun s => ae_all_iff.mpr fun t => hpair s t
  filter_upwards [hcount] with ω hω
  intro s t hst
  rcases hst.eq_or_lt with rfl | hlt
  · exact le_rfl
  obtain ⟨u, hu⟩ := dense_right_sequence K hKdense s
  obtain ⟨v, hv⟩ := dense_right_sequence K hKdense t
  have horder : ∀ᶠ n in atTop, (u n : ℝ≥0) < (v n : ℝ≥0) :=
    (hu.mono_right nhdsWithin_le_nhds).eventually_lt (hv.mono_right nhdsWithin_le_nhds) hlt
  exact le_of_tendsto_of_tendsto
    ((A.rightCont ω t).tendsto.comp hv) ((A.rightCont ω s).tendsto.comp hu)
    (horder.mono fun n hn => hω (u n) (v n) hn.le)
