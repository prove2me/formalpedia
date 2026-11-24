-- Prove2me | solution 1 for GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T02:25:35.482293+00:00
-- url     : https://prove2.me/submissions/1f45ac64-2e12-474a-bee0-79e791ee567b

import Mathlib
open Filter Topology


theorem solution : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type) (f : ι → K) (s : K) (I : Finset ι) (ε : ℝ), 0 ≤ ε → HasSum f s → (∀ i, i ∉ I → ‖f i‖ ≤ ε) → ‖s - ∑ i ∈ I, f i‖ ≤ ε := by
  intro K _ _ ι f s I ε hε hf hsmall
  classical
  have hlim : Tendsto (fun J : Finset ι => ∑ j ∈ J, f j) atTop (𝓝 s) := hf
  apply le_of_tendsto ((hlim.sub_const (∑ i ∈ I, f i)).norm)
  filter_upwards [Filter.eventually_ge_atTop I] with J hJ
  change ‖(∑ j ∈ J, f j) - ∑ i ∈ I, f i‖ ≤ ε
  rw [← Finset.sum_sdiff_eq_sub hJ]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε
  exact fun i hi => hsmall i (Finset.mem_sdiff.mp hi).2
