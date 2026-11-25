-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.iteratedDeriv_line_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:06:35.018461+00:00
-- url     : https://prove2.me/submissions/c43927e8-b8a4-4348-aab6-b42e8f01f054

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_AnalyticHypoSeries
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_hasDerivAt_iteratedFDeriv_line

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open scoped ContDiff NNReal ENNReal Topology
open Set Filter
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {f : E → F} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) (x₀ y : E) (k : ℕ) {t : ℝ} (ht : x₀ + t • y ∈ s) :
    iteratedDeriv k (fun τ : ℝ ↦ f (x₀ + τ • y)) t =
      iteratedFDeriv ℝ k f (x₀ + t • y) (fun _ ↦ y) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    have hU : IsOpen {τ : ℝ | x₀ + τ • y ∈ s} := hs.preimage (by fun_prop)
    have hev : iteratedDeriv k (fun τ : ℝ ↦ f (x₀ + τ • y)) =ᶠ[𝓝 t]
        fun τ ↦ iteratedFDeriv ℝ k f (x₀ + τ • y) (fun _ ↦ y) := by
      filter_upwards [hU.mem_nhds ht] with τ hτ using ih hτ
    rw [iteratedDeriv_succ, hev.deriv_eq]
    exact (hasDerivAt_iteratedFDeriv_line hs hf x₀ y k ht).deriv
end GroundTheory.Automorphic.Sobolev
