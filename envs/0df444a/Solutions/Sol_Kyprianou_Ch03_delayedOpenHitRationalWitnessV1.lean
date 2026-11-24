-- Prove2me | solution 1 for Kyprianou.Ch03.delayedOpenHitRationalWitnessV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:02:23.613516+00:00
-- url     : https://prove2.me/submissions/80201100-5e06-4be8-ac86-928fb8910333

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false


theorem solution
    {Omega : Type} (X : NNReal → Omega → Real) (B : Set Real)
    (hB : IsOpen B) (a : NNReal) (omega : Omega)
    (hrc : ∀ t : NNReal, ContinuousWithinAt (fun u => X u omega) (Set.Ici t) t)
    (s : NNReal) :
    sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | a ≤ t ∧ X t omega ∈ B}) < (s : WithTop NNReal) ↔
      ∃ q : ℚ, a ≤ Real.toNNReal q ∧ Real.toNNReal q < s ∧ X (Real.toNNReal q) omega ∈ B := by
  constructor
  · intro h
    obtain ⟨b, ⟨t, ⟨hat, htB⟩, rfl⟩, hts⟩ := sInf_lt_iff.mp h
    have hts' : t < s := WithTop.coe_lt_coe.mp hts
    have hev : ∀ᶠ v in 𝓝[≥] t, X v omega ∈ B :=
      (hrc t).eventually (hB.mem_nhds htB)
    obtain ⟨w, htw, hw⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
    have hmin : (t : ℝ) < min (w : ℝ) s := lt_min (by exact_mod_cast htw) (by exact_mod_cast hts')
    obtain ⟨q, htq, hqm⟩ := exists_rat_btwn hmin
    have hq0 : (0 : ℝ) < q := (NNReal.coe_nonneg t).trans_lt htq
    have htq' : t ≤ Real.toNNReal q := by
      rw [Real.le_toNNReal_iff_coe_le hq0.le]
      exact htq.le
    have hqs : Real.toNNReal q < s := by
      rw [Real.toNNReal_lt_iff_lt_coe hq0.le]
      exact hqm.trans_le (min_le_right _ _)
    refine ⟨q, hat.trans htq', hqs, hw ⟨htq', ?_⟩⟩
    rw [Real.toNNReal_lt_iff_lt_coe hq0.le]
    exact hqm.trans_le (min_le_left _ _)
  · rintro ⟨q, hqa, hqs, hqB⟩
    exact lt_of_le_of_lt (sInf_le ⟨Real.toNNReal q, ⟨hqa, hqB⟩, rfl⟩)
      (WithTop.coe_lt_coe.mpr hqs)

