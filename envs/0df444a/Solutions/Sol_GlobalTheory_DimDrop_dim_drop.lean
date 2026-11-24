-- Prove2me | solution 1 for GlobalTheory.DimDrop.dim_drop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:02:04.401847+00:00
-- url     : https://prove2.me/submissions/85947387-cec5-40dc-8e95-d78c1a4975f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimDropAndFiniteOfDimZero
import Theorems.Thm_GlobalTheory_DimDrop_topologicalKrullDim_lt_of_isClosed
import Theorems.Thm_GlobalTheory_DimDrop_finite_of_topologicalKrullDim_nonpos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TopologicalSpace Order
open GlobalTheory GlobalTheory.DimDrop
namespace GlobalTheory.DimDrop
theorem _root_.solution : ∀ (S : Type) [TopologicalSpace S] [NoetherianSpace S],
    (∀ (C : Set S) (d : ℕ), IsClosed C → topologicalKrullDim S ≤ d →
      (∀ Z ∈ irreducibleComponents S, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z → ¬ Z ⊆ C) →
      topologicalKrullDim C < d) ∧
    (T0Space S → topologicalKrullDim S ≤ 0 → Finite S) := by
  intro S _ _
  exact ⟨fun C d hC hS hZ => topologicalKrullDim_lt_of_isClosed S C d hC hS hZ,
    fun _ h => finite_of_topologicalKrullDim_nonpos S h⟩
end GlobalTheory.DimDrop
