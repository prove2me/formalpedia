-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52StrictUpperClockFactsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:23:52.350808+00:00
-- url     : https://prove2.me/submissions/ecc66c7c-bc66-4e62-93c2-14ba9da66001

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open Kyprianou.Ch05
/-- A finite strict upper crossing of a positive barrier has positive time and reaches at least the barrier. -/
theorem solution
    (Y : NNReal → ℝ) (h0 : Y 0 = 0)
    (hr : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (x : ℝ) (hx : 0 < x) (s : NNReal)
    (hs : (s : WithTop NNReal) = sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ x < Y t}) :
    0 < s ∧ (∀ t : NNReal, t < s → Y t ≤ x) ∧ x ≤ Y s := by
  have hAt : x ≤ Y s := by
    by_contra! hp
    have hpos : ∀ᶠ u in nhdsWithin s (Ici s), Y u < x :=
      (hr s).tendsto.eventually (eventually_lt_nhds hp)
    have hpos' : ∀ᶠ u in nhdsWithin s (Ioi s), Y u < x :=
      hpos.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)
    obtain ⟨r, hsr, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hpos'
    have hlt : (sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ x < Y t}) < (r : WithTop NNReal) := by
      rw [← hs]
      exact WithTop.coe_lt_coe.mpr hsr
    obtain ⟨_, ⟨t, rfl, ht0, ht⟩, htr⟩ := sInf_lt_iff.mp hlt
    have hst : s ≤ t := WithTop.coe_le_coe.mp (by
      rw [hs]
      exact sInf_le ⟨t, rfl, ht0, ht⟩)
    have hst' : s < t := lt_of_le_of_ne hst (fun he => (not_lt_of_ge hp.le) (he ▸ ht))
    exact (not_lt_of_ge (hsub ⟨hst', WithTop.coe_lt_coe.mp htr⟩).le) ht
  have hs0 : 0 < s := by
    by_contra! h
    have he : s = 0 := le_antisymm h bot_le
    rw [he, h0] at hAt
    exact (not_lt_of_ge hAt) hx
  refine ⟨hs0, ?_, hAt⟩
  intro t ht
  by_contra! hn
  have ht0 : 0 < t := by
    by_contra! h
    have he : t = 0 := le_antisymm h bot_le
    rw [he, h0] at hn
    exact (not_lt_of_ge hx.le) hn
  have hle : (s : WithTop NNReal) ≤ ↑t := by
    rw [hs]
    exact sInf_le ⟨t, rfl, ht0, hn⟩
  exact (not_lt_of_ge (WithTop.coe_le_coe.mp hle)) ht
