-- Prove2me | solution 1 for GlobalTheory.DirichletTail.abel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:20.979889+00:00
-- url     : https://prove2.me/submissions/9f68c8e3-6301-4a2a-8232-07051b74dffe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionEqTsumOfOneLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.DirichletTail
open Filter Topology
namespace GlobalTheory.DirichletTail
theorem _root_.solution {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, χ ((n + 1 : ℕ) : ZMod q) * ((n + 1 : ℕ) : ℂ) ^ (-s)
      = ∑ n ∈ Finset.range N, term χ n s
        + (∑ k ∈ Finset.range N, χ ((k + 1 : ℕ) : ZMod q)) * ((N + 1 : ℕ) : ℂ) ^ (-s) := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ, ih, term]
    push_cast
    ring
end GlobalTheory.DirichletTail
