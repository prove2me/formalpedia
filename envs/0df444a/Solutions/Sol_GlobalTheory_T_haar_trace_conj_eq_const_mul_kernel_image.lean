-- Prove2me | solution 1 for GlobalTheory.T.haar_trace_conj_eq_const_mul_kernel_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:24:35.578313+00:00
-- url     : https://prove2.me/submissions/9b3a9156-10df-43ba-b257-57a1ec7d4b47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarTraceConjEqConstMulKernelImage
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarTraceConjEqConstMulKernelImageStatement
import Theorems.Thm_GlobalTheory_RowFubini_haar_trace_conj_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {X Y : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X] [BorelSpace X]
    [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [MeasurableSpace Y] [BorelSpace Y]
    (R N K : Subgroup X) (π : R →* Y) (σ : Y →* R),
    IsClosed (R : Set X) → IsClosed (N : Set X) → N ≤ R → IsOpen (K : Set X) → IsCompact (K : Set X) →
    Continuous π → Continuous σ → (∀ y, π (σ y) = y) → (∀ r : R, π r = 1 ↔ r.1 ∈ N) →
    ∀ ρ : Measure R, ρ.IsHaarMeasure →
    ∃ (κ : ℝ) (la : Measure N) (ν : Measure Y), 0 < κ ∧ la.IsHaarMeasure ∧ ν.IsHaarMeasure ∧ ∀ b : X,
      ρ.real {r : R | b⁻¹ * r.1 * b ∈ K} = κ * la.real {n : N | b⁻¹ * n.1 * b ∈ K} * ν.real (π '' {r : R | b⁻¹ * r.1 * b ∈ K}) := by
  first | exact @GlobalTheory.RowFubini.haar_trace_conj_eq | exact GlobalTheory.RowFubini.haar_trace_conj_eq | (intros; apply GlobalTheory.RowFubini.haar_trace_conj_eq <;> assumption)
end _root_.GlobalTheory.T
