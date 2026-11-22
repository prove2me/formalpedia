-- Prove2me | solution 1 for NemytskiiLebesgue.ae_norm_frechet_ratio_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:37:13.421191+00:00
-- url     : https://prove2.me/submissions/3d45d020-243b-4a37-bd04-73bef5023801

module
public import Mathlib.Analysis.Calculus.MeanValue
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped ENNReal Topology
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ^k)}
    (hff' : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ)
    {l : ℕ → Ω → ℝ^m} (hl : ∀ᵐ ω : Ω ∂μ, Tendsto (l · ω) atTop (𝓝 0))
    (u : Ω → ℝ^m) :
    ∀ᵐ ω : Ω ∂μ, Tendsto
      (fun n : ℕ => ‖f ω (u ω + l n ω) - f ω (u ω) - f' ω (u ω) (l n ω)‖ / ‖l n ω‖)
      atTop
      (𝓝 0) := by
  filter_upwards [hff', hl] with ω hω hω'
  have hffu := hω (u ω)
  rw [hasFDerivAt_iff_tendsto] at hffu
  convert hffu.comp (show Tendsto (fun n : ℕ => u ω + l n ω) atTop (𝓝 (u ω)) by
    simpa using hω'.const_add (u ω)) using 2
  simp [div_eq_inv_mul]
end NemytskiiLebesgue
