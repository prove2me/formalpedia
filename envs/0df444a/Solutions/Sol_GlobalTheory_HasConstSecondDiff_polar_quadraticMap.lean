-- Prove2me | solution 1 for GlobalTheory.HasConstSecondDiff.polar_quadraticMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:56.525226+00:00
-- url     : https://prove2.me/submissions/29fd6650-2401-414a-b1b5-70eb79423852

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
variable {X A : Type*} [AddCommGroup X] [AddCommGroup A]
open GlobalTheory.HasConstSecondDiff
variable {f : X → A}
namespace GlobalTheory.HasConstSecondDiff
theorem _root_.solution (h : HasConstSecondDiff f) (he : ∀ x, f (-x) = f x) (μ ν : X) :
    QuadraticMap.polar (h.quadraticMap he) μ ν = h.bilin μ ν := by
  simp only [QuadraticMap.polar, quadraticMap_apply, h.bilin_apply_zero]
  abel
end GlobalTheory.HasConstSecondDiff
