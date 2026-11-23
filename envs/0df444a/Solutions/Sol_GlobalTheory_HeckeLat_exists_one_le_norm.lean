-- Prove2me | solution 1 for GlobalTheory.HeckeLat.exists_one_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:52.241189+00:00
-- url     : https://prove2.me/submissions/71fa47ee-bed7-4d1d-a90a-a932042ab847

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodicBoundedGaussianSummableCmType

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeLat
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]
namespace GlobalTheory.HeckeLat
theorem _root_.solution {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) {α : 𝓞 K} (hα : α ≠ 0) :
    ∃ i, 1 ≤ ‖φ i (α : K)‖ := by
  by_contra h
  push_neg at h
  have hlt : ∀ w : InfinitePlace K, w (α : K) < 1 := by
    intro w
    obtain ⟨i, hi, -⟩ := hφ w.embedding
    rw [← InfinitePlace.norm_embedding_eq]
    rcases hi with hi | hi
    · rw [hi]; exact h i
    · rw [hi, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]; exact h i
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  exact absurd (InfinitePlace.one_le_of_lt_one hα (fun z _ => hlt z)) (not_le.2 (hlt w))
end GlobalTheory.HeckeLat
