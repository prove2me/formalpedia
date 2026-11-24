-- Prove2me | solution 1 for GlobalTheory.RootEx.isClosedEmbedding_affPt_uncurry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:20:39.885226+00:00
-- url     : https://prove2.me/submissions/5e98a052-e6de-4eee-95cb-2300bfcbb0db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Theorems.Thm_GlobalTheory_RootEx_affPt_of_free
import Theorems.Thm_GlobalTheory_RootEx_affPt_inl_inl
import Theorems.Thm_GlobalTheory_RootEx_continuous_affPt_uncurry

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
theorem _root_.solution [T2Space k] (p : ℕ) :
    IsClosedEmbedding
      fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
        affPt p z.1 z.2 := by
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun M : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k =>
      ((Matrix.of fun r s => M (Sum.inl r) (Sum.inl s) : Matrix n n' k),
        fun rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} =>
          M rs.1.1 rs.1.2 - basePt c (0 : Matrix n n' k) rs.1.1 rs.1.2)) ?_ ?_
    (continuous_affPt_uncurry p)
  · rintro ⟨x, e⟩
    refine Prod.ext ?_ ?_
    · ext r s
      simp [affPt_inl_inl]
    · funext rs
      simp [affPt_of_free]
  · refine Continuous.prodMk (continuous_matrix fun r s => continuous_id.matrix_elem _ _) ?_
    exact continuous_pi fun rs => (continuous_id.matrix_elem _ _).sub continuous_const
end GlobalTheory.RootEx
