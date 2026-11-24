-- Prove2me | solution 1 for GlobalTheory.SCV.hasSum_fderiv_of_locally_normal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:40:56.887676+00:00
-- url     : https://prove2.me/submissions/746bb95c-cd96-48ca-8897-c0e3135e1e4c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_hasSumLocallyUniformlyOn_fderiv
import Theorems.Thm_GlobalTheory_SCV_hasSumLocallyUniformlyOn_of_locally_normal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology ContDiff Nat
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable {ι : Type*} {l : Filter ι} {F : ι → E → V} {f : E → V} {U : Set E}
namespace GlobalTheory.SCV
theorem _root_.solution (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hle : ∀ x ∈ U, ∃ t ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ z ∈ t, ‖F i z‖ ≤ u i)
    {z : E} (hz : z ∈ U) :
    HasSum (fun i => fderiv ℂ (F i) z) (fderiv ℂ (fun w => ∑' i, F i w) z) :=
  (hasSumLocallyUniformlyOn_fderiv hU (hasSumLocallyUniformlyOn_of_locally_normal hle) hF).hasSum hz
end GlobalTheory.SCV
