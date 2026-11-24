-- Prove2me | solution 1 for GlobalTheory.hasConstSecondDiff_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:14.06647+00:00
-- url     : https://prove2.me/submissions/7e9a4736-964b-40de-82b5-d1baf8f38bc6

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
namespace GlobalTheory
theorem _root_.solution (f : X → A) :
    HasConstSecondDiff f ↔ ∀ a μ ν : X,
      f (a + μ + ν) - f (a + μ) - f (a + ν) + f a = f (μ + ν) - f μ - f ν + f 0 := by
  refine ⟨fun h a μ ν => ?_, fun h a a' μ ν => ?_⟩
  · rw [← secondDiff_zero, ← h a 0]; rfl
  · exact (h a μ ν).trans (h a' μ ν).symm
end GlobalTheory
