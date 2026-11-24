-- Prove2me | solution 1 for GlobalTheory.SCV.hasSum_iteratedFDeriv_of_locally_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:54:33.78679+00:00
-- url     : https://prove2.me/submissions/b78d4418-aaf0-4539-b381-e96bc70e59cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_hasSumLocallyUniformlyOn_iteratedFDeriv
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
    (k : ℕ) {z : E} (hz : z ∈ U) :
    HasSum (fun i => iteratedFDeriv ℂ k (F i) z) (iteratedFDeriv ℂ k (fun w => ∑' i, F i w) z) :=
  (hasSumLocallyUniformlyOn_iteratedFDeriv hU (hasSumLocallyUniformlyOn_of_locally_normal hle)
    hF k).hasSum hz
end GlobalTheory.SCV
