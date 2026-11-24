-- Prove2me | solution 1 for GlobalTheory.tendsto_tsum_zero_of_eventually_notMem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:55.854978+00:00
-- url     : https://prove2.me/submissions/ca4634f8-83a5-4afc-ba44-8a8ccd3f73d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K X Y : Type} [NontriviallyNormedField K]
    [IsUltrametricDist K] (τ : X → K) (hτ : Tendsto τ cofinite (𝓝 0)) (f : ℕ → Y → X)
    (hf : ∀ z, τ z ≠ 0 → ∀ᶠ j in atTop, ∀ μ, f j μ ≠ z) :
    Tendsto (fun j => ∑' μ, τ (f j μ)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hS : {z | ¬ ‖τ z‖ < ε / 2}.Finite := by
    have := hτ (Metric.ball_mem_nhds (0 : K) (half_pos hε))
    rw [Filter.mem_map, Filter.mem_cofinite] at this
    convert this using 1
    ext z
    simp
  have hev : ∀ᶠ j in atTop, ∀ z ∈ {z | ¬ ‖τ z‖ < ε / 2}, ∀ μ, f j μ ≠ z :=
    (hS.eventually_all).2 fun z hz => hf z (fun h0 => hz (by rw [h0, norm_zero]; exact half_pos hε))
  filter_upwards [hev] with j hj
  rw [dist_zero_right]
  refine lt_of_le_of_lt
    (IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (half_pos hε).le fun μ => ?_) (half_lt_self hε)
  by_contra h
  exact hj (f j μ) (show ¬ ‖τ (f j μ)‖ < ε / 2 from fun h' => h h'.le) μ rfl
end GlobalTheory
