-- Prove2me | solution 1 for GlobalTheory.SCV.eq_of_invariant_realSubspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:05:37.414731+00:00
-- url     : https://prove2.me/submissions/258a428c-aa3e-442b-96d3-f7a88f891046

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace
import Theorems.Thm_GlobalTheory_SCV_eq_of_invariant_real_lines

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
namespace GlobalTheory.SCV
theorem _root_.solution {f : E → V} {U : Set E} {S : Submodule ℝ E}
    (hS : Submodule.span ℂ (S : Set E) = ⊤) (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U) (h : ∀ z ∈ U, ∀ s ∈ S, z + s ∈ U → f (z + s) = f z)
    {z w : E} (hz : z ∈ U) (hw : w ∈ U) : f z = f w := by
  refine eq_of_invariant_real_lines hS hU hU' hf (fun x hx s hs t ht => h x hx _ ?_ ht) hz hw
  rw [show (t : ℂ) • s = t • s from algebraMap_smul ℂ t s]
  exact S.smul_mem t hs
end GlobalTheory.SCV
