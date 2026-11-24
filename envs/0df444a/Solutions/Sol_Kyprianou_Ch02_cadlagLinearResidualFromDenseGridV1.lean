-- Prove2me | solution 1 for Kyprianou.Ch02.cadlagLinearResidualFromDenseGridV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:21:36.510806+00:00
-- url     : https://prove2.me/submissions/af1eedea-2f35-4ba4-9438-8210e3b659de

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_locallyAbsSummableCumulativeJumpSeriesRightContinuousV1
open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Local cumulative jump-series regularity. -/
theorem solution
    (f : ℝ≥0 → ℝ) (d : ℝ)
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (hf : ∀ t : ℝ≥0, ContinuousWithinAt f (Ici t) t)
    (hs : ∀ T : ℝ≥0, Summable (fun s : Ioc (0 : ℝ≥0) T =>
      |f s - Function.leftLim f s|))
    (heq : ∀ k : ℕ, f (grid k) = d * (grid k : ℝ) +
      ∑' s : Ioc (0 : ℝ≥0) (grid k), (f s - Function.leftLim f s)) :
    ∀ T : ℝ≥0, f T = d * (T : ℝ) +
      ∑' s : Ioc (0 : ℝ≥0) T, (f s - Function.leftLim f s) := by
  let g : ℝ≥0 → ℝ := fun t => d * (t : ℝ) +
    ∑' s : Ioc (0 : ℝ≥0) t, (f s - Function.leftLim f s)
  have hg (t : ℝ≥0) : ContinuousWithinAt g (Ici t) t :=
    (by fun_prop : ContinuousWithinAt (fun u : ℝ≥0 => d * (u : ℝ)) (Ici t) t).add
      (Kyprianou.Ch02.locallyAbsSummableCumulativeJumpSeriesRightContinuousV1
        (fun s => f s - Function.leftLim f s) hs t)
  intro T
  have hsub : Ioi T ⊆ closure (Ioi T ∩ range grid) :=
    hdense.open_subset_closure_inter isOpen_Ioi
  have hT : T ∈ closure (Ioi T ∩ range grid) := by
    apply closure_minimal hsub isClosed_closure
    rw [closure_Ioi]
    exact Set.mem_Ici.mpr le_rfl
  obtain ⟨q, hq, hlim⟩ := mem_closure_iff_seq_limit.mp hT
  have hwithin : Tendsto q atTop (𝓝[Ici T] T) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hlim, Eventually.of_forall (fun n =>
        Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp (hq n).1)))⟩
  have hpoint (n : ℕ) : f (q n) = g (q n) := by
    obtain ⟨k, hk⟩ := (hq n).2
    rw [← hk]
    exact heq k
  have hfLim : Tendsto (fun n => f (q n)) atTop (𝓝 (f T)) :=
    (show Tendsto f (𝓝[Ici T] T) (𝓝 (f T)) from hf T).comp hwithin
  have hgLim : Tendsto (fun n => f (q n)) atTop (𝓝 (g T)) :=
    ((show Tendsto g (𝓝[Ici T] T) (𝓝 (g T)) from hg T).comp hwithin).congr (fun n => (hpoint n).symm)
  exact tendsto_nhds_unique hfLim hgLim
