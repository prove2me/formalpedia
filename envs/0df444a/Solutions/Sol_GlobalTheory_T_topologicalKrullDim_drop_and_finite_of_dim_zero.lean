-- Prove2me | solution 1 for GlobalTheory.T.topologicalKrullDim_drop_and_finite_of_dim_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:33:59.196138+00:00
-- url     : https://prove2.me/submissions/dca1350d-4fa5-479f-8b85-a2c684f23149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimDropAndFiniteOfDimZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimDropAndFiniteOfDimZeroStatement
import Theorems.Thm_GlobalTheory_DimDrop_dim_drop


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TopologicalSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S : Type) [TopologicalSpace S] [NoetherianSpace S], (∀ (C : Set S) (d : ℕ), IsClosed C → topologicalKrullDim S ≤ d → (∀ Z ∈ irreducibleComponents S, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z → ¬ Z ⊆ C) → topologicalKrullDim C < d) ∧ (T0Space S → topologicalKrullDim S ≤ 0 → Finite S) := by
  first | exact @GlobalTheory.DimDrop.dim_drop | exact GlobalTheory.DimDrop.dim_drop | (intros; apply GlobalTheory.DimDrop.dim_drop <;> assumption)
end _root_.GlobalTheory.T
