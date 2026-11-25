-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.hasDerivAt_iteratedFDeriv_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:00:24.622287+00:00
-- url     : https://prove2.me/submissions/2421e37d-0e87-4bc7-975e-363eb9e8d9b4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_AnalyticHypoSeries

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
    HasDerivAt (fun τ : ℝ ↦ iteratedFDeriv ℝ k f (x₀ + τ • y) (fun _ ↦ y))
      (iteratedFDeriv ℝ (k + 1) f (x₀ + t • y) (fun _ ↦ y)) t := by
  have hz : HasDerivAt (fun τ : ℝ ↦ x₀ + τ • y) y t := by
    simpa using ((hasDerivAt_id t).smul_const y).const_add x₀
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) (x₀ + t • y) :=
    (hf.contDiffAt (hs.mem_nhds ht)).differentiableAt_iteratedFDeriv (by
      exact_mod_cast ENat.natCast_lt_top k)
  have h1 := hd.hasFDerivAt.comp_hasDerivAt t hz
  have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) F
    (fun _ ↦ y)).hasFDerivAt.comp_hasDerivAt t h1
  have e : iteratedFDeriv ℝ (k + 1) f (x₀ + t • y) (fun _ ↦ y) =
      (fderiv ℝ (iteratedFDeriv ℝ k f) (x₀ + t • y) y) (fun _ ↦ y) := by
    rw [iteratedFDeriv_succ_apply_left]; rfl
  rw [e]
  exact h2
end GroundTheory.Automorphic.Sobolev
