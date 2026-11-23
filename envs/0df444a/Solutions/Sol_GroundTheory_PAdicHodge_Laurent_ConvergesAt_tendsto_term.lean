-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.ConvergesAt.tendsto_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:38.309277+00:00
-- url     : https://prove2.me/submissions/37c6ba04-61ed-4d40-a911-f755b931057c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Filter Topology
open GroundTheory.PAdicHodge.Laurent
set_option linter.unusedSectionVars false
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {a b c : ℤ → K} {ρ : ℝ}
namespace GroundTheory.PAdicHodge.Laurent
namespace ConvergesAt
theorem _root_.solution (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ)
    (n : ℤ) : Tendsto (fun i => a i * b (n - i)) cofinite (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hinj : Function.Injective (fun i : ℤ => (i, n - i)) := fun i j h => (Prod.ext_iff.1 h).1
  have := ((tendsto_weight_prod ha hb).comp hinj.tendsto_cofinite).div_const (ρ ^ n)
  rw [zero_div] at this
  refine this.congr fun i => ?_
  simp only [Function.comp, norm_mul_term (a := a) (b := b) hρ.ne' n i]
end ConvergesAt
end GroundTheory.PAdicHodge.Laurent
