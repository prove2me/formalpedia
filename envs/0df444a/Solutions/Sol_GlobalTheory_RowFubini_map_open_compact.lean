-- Prove2me | solution 1 for GlobalTheory.RowFubini.map_open_compact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:41.186289+00:00
-- url     : https://prove2.me/submissions/da08adb1-6aa9-4208-9f57-93201a57887b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarTraceConjEqConstMulKernelImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise ENNReal
open GlobalTheory GlobalTheory.RowFubini
variable {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
namespace GlobalTheory.RowFubini
theorem _root_.solution {Y : Type*} [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
    (A : Subgroup X) (π : X →* Y) (σ : Y →* X) (hπ : Continuous π) (hσ : Continuous σ)
    (hsec : ∀ y, π (σ y) = y) (hAo : IsOpen (A : Set X)) (hAc : IsCompact (A : Set X)) :
    IsOpen ((A.map π : Subgroup Y) : Set Y) ∧ IsCompact ((A.map π : Subgroup Y) : Set Y) := by
  refine ⟨Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_, ?_⟩
  · refine Filter.mem_of_superset ((hAo.preimage hσ).mem_nhds ?_) ?_
    · simp [A.one_mem]
    · intro y hy
      exact Subgroup.mem_map.mpr ⟨σ y, hy, hsec y⟩
  · rw [Subgroup.coe_map]
    exact hAc.image hπ
end GlobalTheory.RowFubini
