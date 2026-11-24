-- Prove2me | solution 2 for GlobalTheory.LatticeIndicator.forall_mem_range_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:34.904801+00:00
-- url     : https://prove2.me/submissions/a5fcf782-0d85-45a4-989a-f684e88f0c47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsEqSumIndicatorOfRightInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open GlobalTheory.LatticeIndicator
namespace GlobalTheory.LatticeIndicator
theorem _root_.solution {O K m n : Type*} [CommRing O] [CommRing K] [Algebra O K]
    (x : Matrix m n K) :
    (∀ i j, x i j ∈ (algebraMap O K).range) ↔
      ∃ y : Matrix m n O, y.map (algebraMap O K) = x := by
  constructor
  · intro h
    choose y hy using h
    exact ⟨Matrix.of y, Matrix.ext hy⟩
  · rintro ⟨y, rfl⟩ i j
    exact ⟨y i j, rfl⟩
end GlobalTheory.LatticeIndicator
