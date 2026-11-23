-- Prove2me | solution 1 for GlobalTheory.RootEx.continuous_affPt_uncurry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:35.991982+00:00
-- url     : https://prove2.me/submissions/5d3befe9-0a0f-4669-9e01-8f528d1c798e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Theorems.Thm_GlobalTheory_RootEx_affPt_of_free

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx
variable {k : Type*} [Field k] {n n' : Type*} {c : ℕ}
variable [TopologicalSpace k] [IsTopologicalRing k]
namespace GlobalTheory.RootEx
theorem _root_.solution (p : ℕ) :
    Continuous fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
      affPt p z.1 z.2 := by
  refine continuous_matrix fun r s => ?_
  by_cases h : Free p (r, s)
  · have := fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
      affPt_of_free p z.1 z.2 ⟨(r, s), h⟩
    simp only at this
    simp only [this]
    fun_prop
  · simp only [affPt, Matrix.add_apply, Matrix.of_apply, dif_neg h, add_zero]
    rcases r with r | r <;> rcases s with s | s
    · exact continuous_fst.matrix_elem r s
    all_goals exact continuous_const
end GlobalTheory.RootEx
