-- Prove2me | solution 1 for JHolomorphic.contDiff_mul_of_tsupport_subset
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T13:53:14.828804+00:00
-- url     : https://prove2.me/submissions/83cb360e-e2f3-4641-9ff0-f9de750333d4

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp



namespace JHolomorphic

open MeasureTheory Filter Topology
open scoped ContDiff

/-- The product of a `Cⁿ` function with closed support in an open set `U` and a function that
is `Cⁿ` on `U` is `Cⁿ` on all of `ℂ`. -/
theorem contDiff_mul_of_tsupport_subset_aux {U : Set ℂ} (hU : IsOpen U) {n : ℕ∞} {φ a : ℂ → ℝ}
    (hφ : ContDiff ℝ n φ) (hφU : tsupport φ ⊆ U) (ha : ContDiffOn ℝ n a U) :
    ContDiff ℝ n (fun z => φ z * a z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ U
  · exact hφ.contDiffAt.mul (ha.contDiffAt (hU.mem_nhds hz))
  · have h0 : φ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp fun h => hz (hφU h)
    have : (fun z => φ z * a z) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [h0] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq this

end JHolomorphic

open JHolomorphic

open MeasureTheory Filter Topology
open scoped ContDiff

theorem solution {U : Set ℂ} (hU : IsOpen U) {n : ℕ∞} {φ a : ℂ → ℝ}
    (hφ : ContDiff ℝ n φ) (hφU : tsupport φ ⊆ U) (ha : ContDiffOn ℝ n a U) :
    ContDiff ℝ n (fun z => φ z * a z) :=
  contDiff_mul_of_tsupport_subset_aux hU hφ hφU ha
