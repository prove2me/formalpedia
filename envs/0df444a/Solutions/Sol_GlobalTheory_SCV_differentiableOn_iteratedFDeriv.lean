-- Prove2me | solution 1 for GlobalTheory.SCV.differentiableOn_iteratedFDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:32.42941+00:00
-- url     : https://prove2.me/submissions/2b9222af-ddb4-4a22-a5f2-80d550b501c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_contDiffOn_nat

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
namespace GlobalTheory.SCV
theorem _root_.solution {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (n : ℕ) : DifferentiableOn ℂ (iteratedFDeriv ℂ n f) U :=
  fun _ hx => (((contDiffOn_nat hU (n + 1) hf).contDiffAt
    (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (by exact_mod_cast Nat.lt_succ_self n)).differentiableWithinAt
end GlobalTheory.SCV
