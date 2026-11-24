-- Prove2me | solution 1 for Kyprianou.Ch02.cadlagMonotoneOfDenseSequenceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:39:28.655228+00:00
-- url     : https://prove2.me/submissions/b8dc1a1d-57d8-4794-b109-f9a198d05eca

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false
open Filter Topology Set

theorem solution
    (f : ℝ≥0 → ℝ) (hc : ProbabilityTheory.IsCadlag f)
    (ts : ℕ → ℝ≥0) (hdense : DenseRange ts)
    (hsched : ∀ i j : ℕ, ts i ≤ ts j → f (ts i) ≤ f (ts j))
    (s t : ℝ≥0) (hst : s < t) :
    f s ≤ f t := by
  obtain ⟨u, _, hu, hu_tendsto⟩ :=
    (show Dense (Set.range ts) from hdense).exists_seq_strictAnti_tendsto s
  obtain ⟨v, _, hv, hv_tendsto⟩ :=
    (show Dense (Set.range ts) from hdense).exists_seq_strictAnti_tendsto t
  have hOrder : ∀ᶠ n : ℕ in atTop, u n ≤ v n :=
    (hu_tendsto.eventually_lt hv_tendsto hst).mono (fun _ h => le_of_lt h)
  have huWithin : Tendsto u atTop (𝓝[Set.Ici s] s) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hu_tendsto, Filter.Eventually.of_forall
        (fun n => Set.mem_Ici.mpr (le_of_lt (hu n).1))⟩
  have hvWithin : Tendsto v atTop (𝓝[Set.Ici t] t) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hv_tendsto, Filter.Eventually.of_forall
        (fun n => Set.mem_Ici.mpr (le_of_lt (hv n).1))⟩
  have hxU : Tendsto (fun n => f (u n)) atTop (𝓝 (f s)) :=
    Filter.Tendsto.comp (hc s).1 huWithin
  have hxV : Tendsto (fun n => f (v n)) atTop (𝓝 (f t)) :=
    Filter.Tendsto.comp (hc t).1 hvWithin
  apply le_of_tendsto_of_tendsto hxU hxV
  filter_upwards [hOrder] with n hOrdered
  obtain ⟨i, hi⟩ := (hu n).2
  obtain ⟨j, hj⟩ := (hv n).2
  have hij : ts i ≤ ts j := by simpa only [hi, hj] using hOrdered
  rw [← hi, ← hj]
  exact hsched i j hij
