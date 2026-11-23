-- Prove2me | solution 1 for GlobalTheory.WittIntegrality.mem_S
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:41.165092+00:00
-- url     : https://prove2.me/submissions/f6232dad-2622-447a-a678-f9d13640b016

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittMatrixCoeffMemOfFrobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries Pointwise
open GlobalTheory
open GlobalTheory.WittIntegrality
open WittVector
variable {C : Type} [Field C] (A : ValuationSubring C)
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
namespace GlobalTheory.WittIntegrality
theorem _root_.solution (x : WittVector p C) : x ∈ S A p ↔ ∀ k, x.coeff k ∈ A := by
  constructor
  · rintro ⟨y, rfl⟩ k
    rw [WittVector.map_coeff]
    exact (y.coeff k).2
  · intro h
    refine ⟨WittVector.mk p fun k => ⟨x.coeff k, h k⟩, ?_⟩
    ext k
    rw [WittVector.map_coeff]
    rfl
end GlobalTheory.WittIntegrality
