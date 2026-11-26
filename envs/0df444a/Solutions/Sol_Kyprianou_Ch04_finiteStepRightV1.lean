-- Prove2me | solution 1 for Kyprianou.Ch04.finiteStepRightV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:23:05.795223+00:00
-- url     : https://prove2.me/submissions/a65086ff-d3a8-46ff-8df0-db84f80c7a5a

import Mathlib
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Compact-window finite-step representation implies right continuity. -/
theorem solution {ι : Type} (U : NNReal → ℝ)
    (hU : ∀ n : ℕ, ∃ (s : Finset ι) (r a : ι → ℝ),
      ∀ t : NNReal, t ≤ (n : NNReal) →
        U t = ∑ i ∈ s, if r i ≤ (t : ℝ) then a i else 0) :
    ∀ t : NNReal, Tendsto U (𝓝[>] t) (𝓝 (U t)) := by
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt t
  obtain ⟨s,r,a,hs⟩ := hU n
  have ht : ∀ᶠ v in 𝓝[>] t, v ≤ (n : NNReal) :=
    (show ∀ᶠ v : NNReal in 𝓝[>] t, v ∈ Iio (n : NNReal) from
      nhdsWithin_le_nhds (Iio_mem_nhds hn)).mono fun v hv => hv.le
  have hcell (i : ι) :
      ∀ᶠ v : NNReal in 𝓝[>] t, (if r i ≤ (v : ℝ) then a i else 0) =
        (if r i ≤ (t : ℝ) then a i else 0) := by
    by_cases hi : r i ≤ (t : ℝ)
    · filter_upwards [self_mem_nhdsWithin (a := t) (s := Ioi t)] with v hv
      have hv' : r i ≤ (v : ℝ) := hi.trans (NNReal.coe_le_coe.mpr hv.le)
      simp [hi,hv']
    · have hlt : (t : ℝ) < r i := lt_of_not_ge hi
      have h : ∀ᶠ v : NNReal in 𝓝 t, (v : ℝ) < r i :=
        (NNReal.continuous_coe.tendsto t).eventually (Iio_mem_nhds hlt)
      filter_upwards [nhdsWithin_le_nhds h] with v hv
      simp [hi, not_le_of_gt hv]
  have hsum : ∀ᶠ v : NNReal in 𝓝[>] t, ∀ i ∈ s,
      (if r i ≤ (v : ℝ) then a i else 0) =
        (if r i ≤ (t : ℝ) then a i else 0) :=
    (Filter.eventually_all_finset s).2 (fun i _ => hcell i)
  have he : U =ᶠ[𝓝[>] t] fun _ => U t := by
    filter_upwards [ht,hsum] with v hv hvs
    rw [hs v hv, hs t hn.le]
    exact Finset.sum_congr rfl hvs
  exact tendsto_const_nhds.congr' he.symm
