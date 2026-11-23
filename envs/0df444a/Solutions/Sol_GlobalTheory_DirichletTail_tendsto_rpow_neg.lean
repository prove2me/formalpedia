-- Prove2me | solution 1 for GlobalTheory.DirichletTail.tendsto_rpow_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:21.512599+00:00
-- url     : https://prove2.me/submissions/69d27716-9099-44b3-be78-b2866d5c8ce6

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
theorem _root_.solution {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    Tendsto (fun n : ℕ => ((n + N + 1 : ℕ) : ℝ) ^ (-δ)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ ↦ ((n + N + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat (N + 1)).congr fun n ↦ by omega)
  exact (tendsto_rpow_neg_atTop hδ).comp h
end GlobalTheory.DirichletTail
