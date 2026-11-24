-- Prove2me | solution 1 for GlobalTheory.LocWeil.DerComm.eq_zero_of_tendsto_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:48:49.126812+00:00
-- url     : https://prove2.me/submissions/68383732-7356-4d41-b656-cc548c0dad14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtOneParameter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open GlobalTheory GlobalTheory.LocWeil GlobalTheory.LocWeil.DerComm
namespace GlobalTheory.LocWeil.DerComm
theorem _root_.solution {g h : ℕ → ℝ → ℂ} {m : ℝ → ℂ} (hd : ∀ n s, HasDerivAt (g n) (h n s) s)
    (hc : ∀ n, Continuous (h n)) (hm : Continuous m) (hg : ∀ s, Tendsto (fun n => g n s) atTop (𝓝 0))
    (hh : ∀ s, Tendsto (fun n => h n s) atTop (𝓝 (m s))) : m = 0 := by
  have hden := dense_iUnion_interior_of_closed (f := fun k : ℕ => {s : ℝ | ∀ n, ‖h n s‖ ≤ k})
    (fun k => by
      rw [Set.setOf_forall]
      exact isClosed_iInter fun n => isClosed_le (hc n).norm continuous_const)
    (Set.eq_univ_of_forall fun s => by
      obtain ⟨C, hC⟩ := (hh s).norm.bddAbove_range
      obtain ⟨k, hk⟩ := exists_nat_ge C
      exact Set.mem_iUnion.2 ⟨k, fun n => (hC ⟨n, rfl⟩).trans hk⟩)
  refine hm.ext_on hden continuous_const fun x hx => ?_
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hx
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hk)
  have h1 : (fun b => ∫ s in x..b, m s) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [Metric.ball_mem_nhds x hr] with b hb'
    have h2 : Tendsto (fun n => ∫ s in x..b, h n s) atTop (𝓝 (∫ s in x..b, m s)) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (k : ℝ))
        (Eventually.of_forall fun n => (hc n).aestronglyMeasurable)
        (Eventually.of_forall fun n => Eventually.of_forall fun s hs => hb ?_ n) intervalIntegrable_const
        (Eventually.of_forall fun s _ => hh s)
      exact (convex_ball x r).ordConnected.uIcc_subset (Metric.mem_ball_self hr) hb' (Set.uIoc_subset_uIcc hs)
    have h3 := (hg b).sub (hg x)
    rw [sub_zero] at h3
    refine tendsto_nhds_unique h2 (h3.congr fun n => ?_)
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd n s) ((hc n).intervalIntegrable _ _)).symm
  exact (hm.integral_hasStrictDerivAt x x).hasDerivAt.unique ((hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq h1)
end GlobalTheory.LocWeil.DerComm
